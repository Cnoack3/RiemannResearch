import RiemannResearch.NumberTheory.DirichletExponentialBounds
import RiemannResearch.NumberTheory.DirichletExponentialPrimePowers

/-!
# Local generalized-divisor moments

Source: the user-provided Pareto argument, conversation of 2026-11-13.
The negative-binomial generating series gives the local Dirichlet series;
squaring its nonnegative sum bounds the local second-moment Euler factor.
-/

open scoped BigOperators

namespace RiemannResearch.NumberTheory.DirichletExponential

/-- The squared Dirichlet coefficient with the slightly larger weight `1/n²`. -/
noncomputable def divisorMomentTerm (r n : ℕ) : ℝ :=
  ((zetaReal ^ r) n) ^ 2 / (n : ℝ) ^ 2

theorem divisorMomentTerm_nonneg (r n : ℕ) : 0 ≤ divisorMomentTerm r n := by
  exact div_nonneg (sq_nonneg _) (sq_nonneg _)

@[simp] theorem divisorMomentTerm_zero (r : ℕ) : divisorMomentTerm r 0 = 0 := by
  simp [divisorMomentTerm]

@[simp] theorem divisorMomentTerm_one (r : ℕ) : divisorMomentTerm r 1 = 1 := by
  simp [divisorMomentTerm, (zetaReal_pow_isMultiplicative r).map_one]

theorem divisorMomentTerm_mul (r : ℕ) {m n : ℕ} (hmn : m.Coprime n) :
    divisorMomentTerm r (m * n) = divisorMomentTerm r m * divisorMomentTerm r n := by
  simp only [divisorMomentTerm,
    (zetaReal_pow_isMultiplicative r).map_mul_of_coprime hmn,
    Nat.cast_mul, mul_pow, div_mul_div_comm]

/-- The local Dirichlet series of the generalized divisor function. -/
theorem hasSum_zetaReal_pow_prime_power_scaled {p : ℕ} (hp : p.Prime)
    (r : ℕ) (hr : 1 ≤ r) :
    HasSum (fun a : ℕ => (zetaReal ^ r) (p ^ a) / (p : ℝ) ^ a)
      (((p : ℝ) / ((p : ℝ) - 1)) ^ r) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hq : ‖1 / (p : ℝ)‖ < 1 := by
    rw [Real.norm_of_nonneg (by positivity : 0 ≤ 1 / (p : ℝ))]
    exact (div_lt_one hp0).2 hp1
  have hid : 1 / (1 - 1 / (p : ℝ)) = (p : ℝ) / ((p : ℝ) - 1) := by
    have hpne : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp [hp0.ne', hpne] <;> ring
  have hseries : HasSum
      (fun a : ℕ => ((a + r).choose r : ℝ) * (1 / (p : ℝ)) ^ a)
      (1 / (1 - 1 / (p : ℝ)) ^ (r + 1)) :=
    hasSum_choose_mul_geometric_of_norm_lt_one r hq
  rw [← one_div_pow, hid] at hseries
  apply hseries.congr
  intro s
  apply Finset.sum_congr rfl
  intro a ha
  dsimp only
  rw [zetaReal_pow_succ_prime_pow hp]
  simp [div_eq_mul_inv, one_div]

/-- A nonnegative summable sequence is square summable, with the elementary
bound obtained by expanding the square of its sum. -/
theorem summable_square_and_tsum_le_square {a : ℕ → ℝ} {A : ℝ}
    (ha : HasSum a A) (ha0 : ∀ n, 0 ≤ a n) :
    Summable (fun n => a n ^ 2) ∧ (∑' n, a n ^ 2) ≤ A ^ 2 := by
  have hle : ∀ n, a n ≤ A := fun n => le_hasSum ha n (fun j _ => ha0 j)
  have hterm : ∀ n, a n ^ 2 ≤ A * a n := by
    intro n
    simpa only [pow_two] using mul_le_mul_of_nonneg_right (hle n) (ha0 n)
  have hdom : Summable (fun n => A * a n) := ha.summable.mul_left A
  have hs : Summable (fun n => a n ^ 2) :=
    Summable.of_nonneg_of_le (fun n => sq_nonneg _) hterm hdom
  refine ⟨hs, ?_⟩
  calc
    (∑' n, a n ^ 2) ≤ ∑' n, A * a n := hs.tsum_le_tsum hterm hdom
    _ = A ^ 2 := by rw [tsum_mul_left, ha.tsum_eq, pow_two]

/-- The local Euler factor has the small-prime bound obtained from the square
of the ordinary local Dirichlet series. -/
theorem divisorMomentTerm_prime_local_small {p : ℕ} (hp : p.Prime)
    (r : ℕ) (hr : 1 ≤ r) :
    Summable (fun a : ℕ => ‖divisorMomentTerm r (p ^ a)‖) ∧
      (∑' a : ℕ, divisorMomentTerm r (p ^ a)) ≤
        (((p : ℝ) / ((p : ℝ) - 1)) ^ 2) ^ r := by
  have hscaled := hasSum_zetaReal_pow_prime_power_scaled hp r hr
  have hnonneg : ∀ a : ℕ, 0 ≤ (zetaReal ^ r) (p ^ a) / (p : ℝ) ^ a := by
    intro a
    rw [zetaReal_pow_prime_pow hp]
    positivity
  obtain ⟨hs, hbound⟩ := summable_square_and_tsum_le_square hscaled hnonneg
  have hterm (a : ℕ) : divisorMomentTerm r (p ^ a) =
      ((zetaReal ^ r) (p ^ a) / (p : ℝ) ^ a) ^ 2 := by
    simp only [divisorMomentTerm, Nat.cast_pow, div_pow]
  constructor
  · have hs' : Summable (fun a : ℕ => divisorMomentTerm r (p ^ a)) :=
      hs.congr fun a => (hterm a).symm
    exact hs'.congr fun a =>
      (Real.norm_of_nonneg (divisorMomentTerm_nonneg r (p ^ a))).symm
  · simp_rw [hterm]
    simpa only [← pow_mul, Nat.mul_comm r 2] using hbound

end RiemannResearch.NumberTheory.DirichletExponential
