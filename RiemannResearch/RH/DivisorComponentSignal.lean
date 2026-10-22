import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
The signal of the complete divisor component is the classical totient ratio.
The proof is Möbius inversion of `Nat.sum_totient`; no analytic hypothesis
or assertion about zeros of zeta enters this arithmetic identity.
-/

open scoped BigOperators

namespace RiemannResearch.RH

/-- Exact signal of the finite divisor component. -/
theorem divisor_moebius_signal_eq_totient_div {D : ℕ} (hD : 0 < D) :
    (∑ d ∈ D.divisors, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) =
      (Nat.totient D : ℝ) / (D : ℝ) := by
  have hsum : ∀ n : ℕ, 0 < n →
      (∑ d ∈ n.divisors, (Nat.totient d : ℝ)) = (n : ℝ) := by
    intro n _hn
    exact_mod_cast Nat.sum_totient n
  have hconv := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun n => (Nat.totient n : ℝ)) (g := fun n => (n : ℝ))).mp hsum D hD
  rw [Nat.sum_divisorsAntidiagonal
    (fun x y : ℕ => (ArithmeticFunction.moebius x : ℝ) * (y : ℝ))] at hconv
  have hDne : (D : ℝ) ≠ 0 := by positivity
  apply (eq_div_iff hDne).mpr
  rw [Finset.sum_mul]
  calc
    (∑ d ∈ D.divisors, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) * (D : ℝ)) =
        ∑ d ∈ D.divisors, (ArithmeticFunction.moebius d : ℝ) * ((D / d : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
      have hdne : (d : ℝ) ≠ 0 := by positivity
      have he : (d : ℝ) * ((D / d : ℕ) : ℝ) = (D : ℝ) := by
        exact_mod_cast Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
      calc
        (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) * (D : ℝ) =
            (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) *
              ((d : ℝ) * ((D / d : ℕ) : ℝ)) := by rw [he]
        _ = (ArithmeticFunction.moebius d : ℝ) * ((D / d : ℕ) : ℝ) := by
          field_simp [hdne] <;> ring
    _ = (Nat.totient D : ℝ) := hconv

/-- Every positive divisor conductor has a strictly nonzero obstruction signal. -/
theorem divisor_moebius_signal_pos {D : ℕ} (hD : 0 < D) :
    0 < ∑ d ∈ D.divisors, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) := by
  rw [divisor_moebius_signal_eq_totient_div hD]
  apply div_pos
  · exact_mod_cast Nat.totient_pos.mpr hD
  · exact_mod_cast hD

end RiemannResearch.RH
