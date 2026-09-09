import RiemannResearch.RH.BinaryWaveletPrimitive

/-!
# Exact support of nearby integer dilation discrepancies

Source: user-provided argument `analytic_wavelet_foothold.md`, §8.
This support theorem keeps the threshold intervals explicitly; no claim
about discarding overlapping intervals is made.
-/

namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Before a finite threshold, unequal wavelet values must cross one of
the indicated integer dilation boundaries. -/
theorem binaryWavelet_nearby_mismatch_support (m n J k : ℕ)
    (hm : 0 < m) (hmn : m ≤ n) (hk : k < m*J)
    (hne : dilationWaveletSequence 2 m k ≠ dilationWaveletSequence 2 n k) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ J ∧ m*j ≤ k ∧ k < n*j := by
  have hn : 0 < n := lt_of_lt_of_le hm hmn
  have hqle : k/n ≤ k/m := by
    apply (Nat.le_div_iff_mul_le hm).2
    calc
      (k/n)*m ≤ (k/n)*n := Nat.mul_le_mul_left _ hmn
      _ ≤ k := Nat.div_mul_le_self k n
  have hqne : k/n ≠ k/m := by
    intro he
    apply hne
    rw [dilationWaveletSequence_two_pullback m k,
      dilationWaveletSequence_two_pullback n k, he]
  have hq : k/n < k/m := by omega
  have hJ : k/m < J :=
    (Nat.div_lt_iff_lt_mul hm).2 (by simpa only [Nat.mul_comm J m] using hk)
  refine ⟨k/n+1, Nat.succ_le_succ (Nat.zero_le _), by omega, ?_, ?_⟩
  · have h : (k/n+1)*m ≤ k := (Nat.le_div_iff_mul_le hm).1 (by omega)
    simpa only [Nat.mul_comm m (k/n+1)] using h
  · have h : k < (k/n+1)*n :=
      (Nat.div_lt_iff_lt_mul hn).1 (Nat.lt_succ_self _)
    simpa only [Nat.mul_comm n (k/n+1)] using h

end
end RiemannResearch.RH.Pareto
