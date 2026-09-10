import RiemannResearch.RH.DampedMobiusCoefficients
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Uniform weighted square energy of the exact damped arithmetic coefficients

Source: `FourierBridgeUniformSignedEnergy20260910.md`, Section 7, (7.2).

The normalization bounds remain explicit scalar hypotheses. The actual signed
Möbius divisor coefficients, the atom at one, and the full infinite weighted
sum are retained. No Mertens discrepancy estimate is used here.
-/

open scoped BigOperators

namespace RiemannResearch.RH.Pareto
noncomputable section

/-- A universal summable majorant for the logarithmic square weight. -/
theorem log_nat_sq_mul_rpow_neg_two_le (n : ℕ) :
    Real.log n ^ 2 * (n : ℝ) ^ (-2 : ℝ) ≤
      16 * (n : ℝ) ^ (-3 / 2 : ℝ) := by
  by_cases hn : n = 0
  · simp [hn]
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
  have hb := Real.log_le_rpow_div hn0.le (by norm_num : (0 : ℝ) < 1 / 4)
  have hb2 : Real.log n ^ 2 ≤ ((n : ℝ) ^ (1 / 4 : ℝ) / (1 / 4)) ^ 2 :=
    pow_le_pow_left₀ hlog hb 2
  have he1 : ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = (n : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    norm_num
  have he2 : (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-2 : ℝ) =
      (n : ℝ) ^ (-3 / 2 : ℝ) := by
    rw [← Real.rpow_add hn0]
    norm_num
  calc
    _ ≤ ((n : ℝ) ^ (1 / 4 : ℝ) / (1 / 4)) ^ 2 * (n : ℝ) ^ (-2 : ℝ) :=
      mul_le_mul_of_nonneg_right hb2 (Real.rpow_nonneg hn0.le _)
    _ = 16 * (((n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 * (n : ℝ) ^ (-2 : ℝ)) := by ring
    _ = _ := by rw [he1, he2]

/-- A uniform positive power majorant, including the distinguished atom at one. -/
theorem normalizedSignedCoefficient_square_majorant {ε N C K : ℝ}
    (hε : 0 ≤ ε) (hN : |N| ≤ C) (hK : |N - 1| ≤ K * ε) (n : ℕ) :
    normalizedSignedCoefficient ε N n ^ 2 * (n : ℝ) ^ (-2 : ℝ) ≤
      ((K ^ 2 + 16 * C ^ 2) * ε ^ 2) * (n : ℝ) ^ (-3 / 2 : ℝ) := by
  by_cases hn0 : n = 0
  · simp [hn0, normalizedSignedCoefficient]
  by_cases hn1 : n = 1
  · subst n
    simp only [normalizedSignedCoefficient_one, Nat.cast_one, Real.one_rpow, mul_one]
    have hb := pow_le_pow_left₀ (abs_nonneg (N - 1)) hK 2
    rw [sq_abs] at hb
    nlinarith [sq_nonneg (C * ε)]
  have hn2 : 2 ≤ n := by omega
  have hab := abs_normalizedSignedCoefficient_le_mul_log hε hN hn2
  have hb := pow_le_pow_left₀ (abs_nonneg (normalizedSignedCoefficient ε N n)) hab 2
  rw [sq_abs] at hb
  have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hpow := Real.rpow_nonneg hn_nonneg (-2 : ℝ)
  have hlog := log_nat_sq_mul_rpow_neg_two_le n
  calc
    _ ≤ (C * ε * Real.log n) ^ 2 * (n : ℝ) ^ (-2 : ℝ) :=
      mul_le_mul_of_nonneg_right hb hpow
    _ = (C ^ 2 * ε ^ 2) * (Real.log n ^ 2 * (n : ℝ) ^ (-2 : ℝ)) := by ring
    _ ≤ (C ^ 2 * ε ^ 2) * (16 * (n : ℝ) ^ (-3 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog (mul_nonneg (sq_nonneg C) (sq_nonneg ε))
    _ ≤ _ := by
      have hpos := mul_nonneg (mul_nonneg (sq_nonneg K) (sq_nonneg ε))
        (Real.rpow_nonneg hn_nonneg (-3 / 2 : ℝ))
      nlinarith

/-- The full arithmetic square energy is summable, with a uniform epsilon-square bound.
Only the two displayed scalar normalization bounds are hypotheses. -/
theorem normalizedSignedCoefficient_weighted_energy {ε N C K : ℝ}
    (hε : 0 ≤ ε) (hN : |N| ≤ C) (hK : |N - 1| ≤ K * ε) :
    Summable (fun n : ℕ => normalizedSignedCoefficient ε N n ^ 2 / (n : ℝ) ^ 2) ∧
      (∑' n : ℕ, normalizedSignedCoefficient ε N n ^ 2 / (n : ℝ) ^ 2) ≤
        ((K ^ 2 + 16 * C ^ 2) *
          (∑' n : ℕ, (n : ℝ) ^ (-3 / 2 : ℝ))) * ε ^ 2 := by
  let D : ℝ := (K ^ 2 + 16 * C ^ 2) * ε ^ 2
  have hpseries : Summable (fun n : ℕ => (n : ℝ) ^ (-3 / 2 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hmajor : Summable (fun n : ℕ => D * (n : ℝ) ^ (-3 / 2 : ℝ)) :=
    hpseries.mul_left D
  have hbound (n : ℕ) : normalizedSignedCoefficient ε N n ^ 2 / (n : ℝ) ^ 2 ≤
      D * (n : ℝ) ^ (-3 / 2 : ℝ) := by
    have h := normalizedSignedCoefficient_square_majorant hε hN hK n
    simpa only [Real.rpow_neg (Nat.cast_nonneg n), Real.rpow_two, div_eq_mul_inv, D]
      using h
  have hsum : Summable (fun n : ℕ =>
      normalizedSignedCoefficient ε N n ^ 2 / (n : ℝ) ^ 2) :=
    Summable.of_nonneg_of_le (fun n => div_nonneg (sq_nonneg _) (sq_nonneg _)) hbound hmajor
  refine ⟨hsum, ?_⟩
  calc
    _ ≤ ∑' n : ℕ, D * (n : ℝ) ^ (-3 / 2 : ℝ) := hsum.tsum_le_tsum hbound hmajor
    _ = D * ∑' n : ℕ, (n : ℝ) ^ (-3 / 2 : ℝ) := tsum_mul_left
    _ = _ := by dsimp [D]; ring

end
end RiemannResearch.RH.Pareto
