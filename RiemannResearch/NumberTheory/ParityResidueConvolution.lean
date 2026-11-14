import RiemannResearch.NumberTheory.DirichletExponential
/-!
# The Dirichlet square of the parity residue
Source: user-provided G2_Dirichlet_Convolution_Pareto_Work_Analysis, 13 November
2026, Sections 1--3 and 7. Products are Mathlib Dirichlet convolution.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.NumberTheory.ParityResidueConvolution
open DirichletExponential

def paritySquare : ArithmeticFunction ℝ := residueAF 2 * residueAF 2

theorem residue_two_eq (n : ℕ) :
    residueAF 2 n = if n % 2 = 1 then (1 : ℝ) / 2 else 0 := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [residueAF_apply, h]

theorem residue_two_mul (a b : ℕ) :
    residueAF 2 a * residueAF 2 b = residueAF 2 (a * b) / 2 := by
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
    norm_num [residueAF_apply, Nat.mul_mod, ha, hb]

theorem paritySquare_eq (n : ℕ) :
    paritySquare n = (n.divisors.card : ℝ) * residueAF 2 n / 2 := by
  rw [paritySquare, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => residueAF 2 a * residueAF 2 b)]
  calc
    (∑ d ∈ n.divisors, residueAF 2 d * residueAF 2 (n / d)) =
        ∑ _d ∈ n.divisors, residueAF 2 n / 2 := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [residue_two_mul, Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
    _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]; ring

theorem paritySquare_parity (n : ℕ) :
    paritySquare n = if n % 2 = 1 then (n.divisors.card : ℝ) / 4 else 0 := by
  rw [paritySquare_eq, residue_two_eq]
  split_ifs <;> ring

theorem paritySquare_not_bounded : ¬ ∃ C : ℝ, ∀ n, |paritySquare n| ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨a, ha⟩ := exists_nat_gt (4 * C)
  have hl := residueAF_square_prime_pow_lower (by decide : Nat.Prime 2)
    (by decide : Nat.Prime 3) (by decide : (2 : ℕ) ≠ 3) a
  have hu := (le_abs_self (paritySquare (3 ^ a))).trans (hC (3 ^ a))
  change ((a : ℝ) + 1) / (2 : ℝ) ^ 2 ≤ paritySquare (3 ^ a) at hl
  norm_num at hl
  linarith

theorem paritySquare_odd_prime_pow {p : ℕ} (hp : p.Prime)
    (hpodd : p % 2 = 1) (a : ℕ) :
    paritySquare (p ^ a) = ((a : ℝ) + 1) / 4 := by
  have hcard : ((p ^ a).divisors.card : ℝ) = (a : ℝ) + 1 := by
    have h : (∑ _d ∈ (p ^ a).divisors, (1 : ℝ)) =
        ∑ _j ∈ Finset.range (a + 1), (1 : ℝ) :=
      Nat.sum_divisors_prime_pow hp
    simpa using h
  rw [paritySquare_parity]
  have hodd : p ^ a % 2 = 1 := by simp [Nat.pow_mod, hpodd]
  rw [if_pos hodd, hcard]

theorem paritySquare_prime {p : ℕ} (hp : p.Prime) (hpodd : p % 2 = 1) :
    paritySquare p = 1 / 2 := by
  convert paritySquare_odd_prime_pow hp hpodd 1 using 1 <;> norm_num

theorem paritySquare_three_pow (a : ℕ) :
    paritySquare (3 ^ a) = ((a : ℝ) + 1) / 4 :=
  paritySquare_odd_prime_pow (by decide) (by decide) a

end RiemannResearch.NumberTheory.ParityResidueConvolution
