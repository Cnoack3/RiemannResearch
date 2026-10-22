import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! Source: user-provided smoothing note §3.1. Finite Dirichlet-convolution
logarithmic derivation and the exact quadratic Möbius-Mangoldt identity.
This generic arithmetic module is consumed by RH.ParetoQuadraticSmoothing. -/
open scoped BigOperators
noncomputable section

namespace ArithmeticFunction

/-- Pointwise logarithmic weighting, a derivation for Dirichlet convolution. -/
def logWeight (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ := log.pmul f

@[simp] theorem logWeight_apply (f : ArithmeticFunction ℝ) (n : ℕ) :
    logWeight f n = Real.log (n : ℝ) * f n := rfl

/-- The finite divisor-convolution Leibniz identity. -/
theorem logWeight_mul (f g : ArithmeticFunction ℝ) :
    logWeight (f * g) = logWeight f * g + f * logWeight g := by
  ext n
  simp only [logWeight_apply, mul_apply, add_apply]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  have hmem := Nat.mem_divisorsAntidiagonal.mp hx
  have hprod : x.1 * x.2 ≠ 0 := by rw [hmem.1]; exact hmem.2
  have ha : (x.1 : ℝ) ≠ 0 := by exact_mod_cast (mul_ne_zero_iff.mp hprod).1
  have hb : (x.2 : ℝ) ≠ 0 := by exact_mod_cast (mul_ne_zero_iff.mp hprod).2
  have hlog : Real.log (n : ℝ) = Real.log (x.1 : ℝ) + Real.log (x.2 : ℝ) := by
    rw [← hmem.1, Nat.cast_mul, Real.log_mul ha hb]
  rw [hlog]
  ring

@[simp] theorem logWeight_neg (f : ArithmeticFunction ℝ) :
    logWeight (-f) = -logWeight f := by
  ext n
  simp [logWeight_apply]

@[simp] theorem logWeight_zeta : logWeight (zeta : ArithmeticFunction ℝ) = log := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp
  · simp [logWeight_apply, natCoe_apply, zeta_apply, hn, log_apply]

/-- The first logarithmic Möbius identity, in convolution form. -/
theorem logWeight_moebius_mul_zeta :
    logWeight (moebius : ArithmeticFunction ℝ) * (zeta : ArithmeticFunction ℝ) =
      -vonMangoldt := by
  ext n
  rw [coe_mul_zeta_apply]
  simpa only [logWeight_apply, intCoe_apply, neg_apply, log_apply, mul_comm] using
    (sum_moebius_mul_log_eq (n := n))

/-- Algebraic quadratic Möbius convolution, retaining the mixed Λ*Λ term. -/
theorem logWeight_twice_moebius_mul_zeta :
    logWeight (logWeight (moebius : ArithmeticFunction ℝ)) *
      (zeta : ArithmeticFunction ℝ) =
        vonMangoldt * vonMangoldt - logWeight vonMangoldt := by
  have hz : (zeta : ArithmeticFunction ℝ) * vonMangoldt = log := by
    ext n
    rw [coe_zeta_mul_apply]
    exact vonMangoldt_sum
  have hcross : logWeight (moebius : ArithmeticFunction ℝ) * log =
      -(vonMangoldt * vonMangoldt) := by
    rw [← hz, ← mul_assoc, logWeight_moebius_mul_zeta]
    exact _root_.neg_mul _ _
  have h := congrArg logWeight logWeight_moebius_mul_zeta
  rw [logWeight_mul, logWeight_zeta, hcross, logWeight_neg] at h
  linear_combination h

/-- Exact second logarithmic moment identity at every integer, including zero. -/
theorem sum_moebius_mul_log_sq (n : ℕ) :
    (∑ d ∈ n.divisors, (moebius d : ℝ) * Real.log (d : ℝ) ^ 2) =
      (vonMangoldt * vonMangoldt) n - vonMangoldt n * Real.log (n : ℝ) := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n)
    logWeight_twice_moebius_mul_zeta
  rw [coe_mul_zeta_apply] at h
  change (∑ d ∈ n.divisors, Real.log (d : ℝ) *
    (Real.log (d : ℝ) * (moebius d : ℝ))) =
      (vonMangoldt * vonMangoldt) n - Real.log (n : ℝ) * vonMangoldt n at h
  calc
    _ = ∑ d ∈ n.divisors, Real.log (d : ℝ) *
        (Real.log (d : ℝ) * (moebius d : ℝ)) := by
      apply Finset.sum_congr rfl
      intro d _
      ring
    _ = _ := by rw [h]; ring

end ArithmeticFunction

end
