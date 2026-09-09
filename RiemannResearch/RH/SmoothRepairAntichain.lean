import RiemannResearch.RH.OneBoundaryRepairObstruction

/-! # The explicit smooth antichain of distributed repair endpoints -/

namespace RiemannResearch.RH.SmoothRepairAntichain

def endpoint (L j : ℕ) : ℕ := 2 ^ j * 3 ^ (L - j)

theorem endpoint_pos (L j : ℕ) : 0 < endpoint L j := by
  unfold endpoint
  positivity

/-- Divisibility within one homogeneous seed layer forces identical indices. -/
theorem endpoint_dvd_iff (L i j : ℕ) (hi : i ≤ L) (hj : j ≤ L) :
    endpoint L i ∣ endpoint L j ↔ i = j := by
  constructor
  · intro hd
    have htwo : 2 ^ i ∣ 2 ^ j := by
      have h1 : 2 ^ i ∣ endpoint L i := ⟨3 ^ (L - i), rfl⟩
      have h2 := dvd_trans h1 hd
      exact (Nat.Coprime.pow i (L - j) (by decide : Nat.Coprime 2 3)).dvd_of_dvd_mul_right h2
    have hthree : 3 ^ (L - i) ∣ 3 ^ (L - j) := by
      have h1 : 3 ^ (L - i) ∣ endpoint L i := by
        refine ⟨2 ^ i, ?_⟩
        unfold endpoint
        ring
      have h2 := dvd_trans h1 hd
      have h3 : 3 ^ (L - i) ∣ 3 ^ (L - j) * 2 ^ j := by
        simpa [endpoint, mul_comm] using h2
      exact (Nat.Coprime.pow (L - i) j (by decide : Nat.Coprime 3 2)).dvd_of_dvd_mul_right h3
    have hij : i ≤ j := by
      by_contra hn
      have hlt := Nat.pow_lt_pow_right (by decide : 1 < 2) (show j < i by omega)
      have hle := Nat.le_of_dvd (by positivity : 0 < 2 ^ j) htwo
      omega
    have hji : L - i ≤ L - j := by
      by_contra hn
      have hlt := Nat.pow_lt_pow_right (by decide : 1 < 3) (show L - j < L - i by omega)
      have hle := Nat.le_of_dvd (by positivity : 0 < 3 ^ (L - j)) hthree
      omega
    omega
  · rintro rfl
    exact dvd_refl _

theorem endpoint_lower (L j : ℕ) (hj : j ≤ L) : 2 ^ L ≤ endpoint L j := by
  have hpow : ∀ n : ℕ, 2 ^ n ≤ 3 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      simpa only [pow_succ] using Nat.mul_le_mul ih (by decide : 2 ≤ 3)
  have h := Nat.mul_le_mul_left (2 ^ j) (hpow (L - j))
  rw [← pow_add, show j + (L - j) = L by omega] at h
  exact h

end RiemannResearch.RH.SmoothRepairAntichain
