import RiemannResearch.RH.SmoothComponentClosedFloor

/-! # Explicit two-seed weights of the genuine arithmetic divisor row -/

namespace RiemannResearch.RH.DivisorComponentJumpRow

noncomputable section

theorem totient_ratio_two_pow (n : ℕ) :
    (Nat.totient (2 ^ n) : ℝ) / (2 ^ n : ℕ) = if n = 0 then 1 else (1 / 2 : ℝ) := by
  cases n with
  | zero => norm_num
  | succ n =>
    rw [totient_ratio_prime_pow_succ 2 n (by decide)]
    norm_num

theorem totient_ratio_three_pow (n : ℕ) :
    (Nat.totient (3 ^ n) : ℝ) / (3 ^ n : ℕ) = if n = 0 then 1 else (2 / 3 : ℝ) := by
  cases n with
  | zero => norm_num
  | succ n =>
    rw [totient_ratio_prime_pow_succ 3 n (by decide)]
    norm_num

/-- The coefficient formula is identified with the existing `jumpWeight`,
which itself was derived from the original Möbius component functional. -/
theorem smooth_jumpWeight (A B i j : ℕ) (hi : i ≤ A) (hj : j ≤ B) :
    jumpWeight (2 ^ A * 3 ^ B) (2 ^ i * 3 ^ j) =
      ((if i = A then 1 else (1 / 2 : ℝ)) *
        (if j = B then 1 else (2 / 3 : ℝ))) / (2 ^ i * 3 ^ j : ℕ) := by
  let D := 2 ^ A * 3 ^ B
  let d := 2 ^ i * 3 ^ j
  let q := 2 ^ (A - i) * 3 ^ (B - j)
  have hD : 0 < D := by dsimp [D]; positivity
  have hd : 0 < d := by dsimp [d]; positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hprod : D = d * q := by
    dsimp [D, d, q]
    have hA : A = i + (A - i) := by omega
    have hB : B = j + (B - j) := by omega
    conv_lhs => rw [hA, hB, pow_add, pow_add]
    ring
  have hmem : d ∈ D.divisors := Nat.mem_divisors.mpr ⟨⟨q, hprod⟩, ne_of_gt hD⟩
  have hquot : D / d = q := by rw [hprod, Nat.mul_div_cancel_left q hd]
  have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hD)
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
  have hprodR : (D : ℝ) = (d : ℝ) * (q : ℝ) := by exact_mod_cast hprod
  have hr : (Nat.totient q : ℝ) / (D : ℝ) =
      ((Nat.totient q : ℝ) / (q : ℝ)) / (d : ℝ) := by
    rw [hprodR]
    ring
  change jumpWeight D d = _
  simp only [jumpWeight, hmem, ↓reduceIte, hquot]
  rw [hr]
  have he : (Nat.totient q : ℝ) / (q : ℝ) =
      (if i = A then 1 else (1 / 2 : ℝ)) * (if j = B then 1 else (2 / 3 : ℝ)) := by
    dsimp [q]
    rw [totient_ratio_mul (2 ^ (A - i)) (3 ^ (B - j))
      (Nat.Coprime.pow (A - i) (B - j) (by decide : Nat.Coprime 2 3)),
      totient_ratio_two_pow, totient_ratio_three_pow]
    have hAi : A - i = 0 ↔ i = A := by omega
    have hBj : B - j = 0 ↔ j = B := by omega
    simp only [hAi, hBj]
  rw [he]

end
end RiemannResearch.RH.DivisorComponentJumpRow
