import RiemannResearch.Analysis.LogarithmicBlockSum

/-!
# Assembly of finite block estimates

Source: user-provided argument, §3 of
`Dyadic_Gram_Prefix_Ordinary_Proof_20260910.md`.
This is the finite grouping step for the proposed rotation prefix bound.
It does not assert the outstanding circular-packing provider.
-/

open scoped BigOperators

namespace Finset

/-- Uniform bounds for consecutive blocks of length at most `q` give a linear
prefix bound whenever the selected block length satisfies `q ≤ N`. No sign
condition on the summands is needed. -/
theorem sum_range_le_two_mul_of_block_bound
    (f : ℕ → ℝ) (N q : ℕ) (hq : 0 < q) (hqN : q ≤ N)
    (L : ℝ) (hL : 0 ≤ L)
    (hblock : ∀ b s : ℕ, s ≤ q → q * b + s ≤ N →
      (∑ i ∈ range s, f (q * b + i)) ≤ L * q) :
    (∑ i ∈ range N, f i) ≤ 2 * L * N := by
  have hfull : ∀ k : ℕ, q * k ≤ N →
      (∑ i ∈ range (q * k), f i) ≤ (k : ℝ) * L * q := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        intro hk
        have hk' : q * k ≤ N := by nlinarith
        have hb := hblock k q le_rfl (by nlinarith : q * k + q ≤ N)
        have hi := ih hk'
        rw [Nat.mul_succ, sum_range_add]
        simp only [Nat.cast_add, Nat.cast_one]
        nlinarith
  have hdiv : q * (N / q) ≤ N := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self N q
  have hrem : N % q ≤ q := Nat.le_of_lt (Nat.mod_lt N hq)
  have he : N = q * (N / q) + N % q := by
    simpa [Nat.mul_comm] using (Nat.div_add_mod N q).symm
  have hr := hblock (N / q) (N % q) hrem (le_of_eq he.symm)
  have hf := hfull (N / q) hdiv
  have hpack : q * (N / q + 1) ≤ 2 * N := by nlinarith
  have hpackR : (q : ℝ) * (((N / q : ℕ) : ℝ) + 1) ≤ 2 * N := by
    exact_mod_cast hpack
  have hp := mul_le_mul_of_nonneg_left hpackR hL
  conv_lhs => rw [he, sum_range_add]
  nlinarith

end Finset
