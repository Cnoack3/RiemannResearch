import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Explicit shifted Möbius source for the compact target

Source: user-provided Green--Pareto--Schur continuation, 6 October 2026,
Section 25 (source formula and bound). The proof splits by divisibility
by 2 and 4. Arithmetic growth is not inferred from the coefficient cap.
-/

namespace RiemannResearch.RH.Pareto.CoefficientStabilization

def compactShiftedMobiusInt (n : ℕ) : ℤ :=
  14 * ArithmeticFunction.moebius n
    - 26 * (if 2 ∣ n then ArithmeticFunction.moebius (n / 2) else 0)
    + 12 * (if 4 ∣ n then ArithmeticFunction.moebius (n / 4) else 0)

noncomputable def compactShiftedMobius (n : ℕ) : ℝ :=
  (compactShiftedMobiusInt n : ℝ)

theorem moebius_even_not_four (n : ℕ)
    (h2 : 2 ∣ n) (h4 : ¬ 4 ∣ n) :
    ArithmeticFunction.moebius n = -ArithmeticFunction.moebius (n / 2) := by
  have hn : n = 2 * (n / 2) := (Nat.mul_div_cancel' h2).symm
  have hn2 : ¬ 2 ∣ n / 2 := by
    rintro ⟨k, hk⟩
    apply h4
    refine ⟨k, ?_⟩
    calc
      n = 2 * (n / 2) := hn
      _ = 4 * k := by rw [hk]; ring
  have hc : (2 : ℕ).Coprime (n / 2) :=
    (Nat.prime_two.coprime_iff_not_dvd).2 hn2
  calc
    ArithmeticFunction.moebius n =
        ArithmeticFunction.moebius (2 * (n / 2)) := congrArg _ hn
    _ = ArithmeticFunction.moebius 2 * ArithmeticFunction.moebius (n / 2) :=
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hc
    _ = -ArithmeticFunction.moebius (n / 2) := by
      rw [ArithmeticFunction.moebius_apply_prime Nat.prime_two]
      ring

theorem moebius_eq_zero_of_four_dvd (n : ℕ) (h4 : 4 ∣ n) :
    ArithmeticFunction.moebius n = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  intro hn
  exact (Nat.squarefree_iff_prime_squarefree.mp hn 2 Nat.prime_two)
    (by simpa using h4)

theorem compactShiftedMobiusInt_abs_le_forty (n : ℕ) :
    |compactShiftedMobiusInt n| ≤ 40 := by
  have hμ (k : ℕ) :
      -(1 : ℤ) ≤ ArithmeticFunction.moebius k ∧
        ArithmeticFunction.moebius k ≤ 1 :=
    abs_le.mp ArithmeticFunction.abs_moebius_le_one
  have hn := hμ n
  have hn2 := hμ (n / 2)
  have hn4 := hμ (n / 4)
  by_cases h2 : 2 ∣ n
  · by_cases h4 : 4 ∣ n
    · have hz := moebius_eq_zero_of_four_dvd n h4
      simp only [compactShiftedMobiusInt, if_pos h2, if_pos h4, hz,
        mul_zero, zero_sub]
      apply abs_le.mpr
      constructor <;> omega
    · have hr := moebius_even_not_four n h2 h4
      simp only [compactShiftedMobiusInt, if_pos h2, if_neg h4, hr,
        mul_zero, add_zero]
      apply abs_le.mpr
      constructor <;> omega
  · have h4 : ¬ 4 ∣ n := by
      intro h
      exact h2 (dvd_trans (by norm_num : (2 : ℕ) ∣ 4) h)
    simp only [compactShiftedMobiusInt, if_neg h2, if_neg h4,
      mul_zero, sub_zero, add_zero]
    apply abs_le.mpr
    constructor <;> omega

theorem compactShiftedMobius_abs_le_forty (n : ℕ) :
    |compactShiftedMobius n| ≤ 40 := by
  unfold compactShiftedMobius
  exact_mod_cast compactShiftedMobiusInt_abs_le_forty n

theorem compactShiftedMobius_formula (n : ℕ) :
    compactShiftedMobius n =
      14 * (ArithmeticFunction.moebius n : ℝ)
        - 26 * (if 2 ∣ n then (ArithmeticFunction.moebius (n / 2) : ℝ) else 0)
        + 12 * (if 4 ∣ n then (ArithmeticFunction.moebius (n / 4) : ℝ) else 0) := by
  simp [compactShiftedMobius, compactShiftedMobiusInt]

theorem compactShiftedMobius_one : compactShiftedMobius 1 = 14 := by
  simp [compactShiftedMobius, compactShiftedMobiusInt]

end RiemannResearch.RH.Pareto.CoefficientStabilization
