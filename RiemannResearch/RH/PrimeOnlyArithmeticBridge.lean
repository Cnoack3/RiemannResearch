import RiemannResearch.RH.PrimeOnlyDyadicEnergy
import RiemannResearch.RH.ActualPrimePowerParetoEnergy
import Lean.Elab.Tactic.Omega

/-! The actual Chebyshev providers apply to exactly the finite arithmetic sums
used in the prime-only signed dyadic identity. -/
noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.PrimeOnlyDyadicEnergy

theorem psi_eq_chebyshev (n : ℕ) : psi n = Chebyshev.psi n := by
  rw [Chebyshev.psi_eq_sum_Icc]
  simp only [Nat.floor_natCast]
  unfold psi
  have hsub : Finset.Icc 1 n ⊆ Finset.Icc 0 n := by
    intro i hi
    simp only [Finset.mem_Icc] at hi ⊢
    omega
  exact Finset.sum_subset hsub (by
    intro i hi hnot
    simp only [Finset.mem_Icc] at hi hnot
    have hi0 : i = 0 := by omega
    subst i
    simp)

theorem primesThrough_eq_primesLE (n : ℕ) : primesThrough n = Nat.primesLE n := by
  ext p
  simp only [primesThrough, Finset.mem_filter, Finset.mem_range, Nat.mem_primesLE,
    Nat.lt_succ_iff]

theorem theta_eq_chebyshev (n : ℕ) : theta n = Chebyshev.theta n := by
  unfold theta
  rw [primesThrough_eq_primesLE, Chebyshev.theta_eq_sum_primesLE_log]

theorem higherPowerError_eq_actual_error (n : ℕ) :
    higherPowerError n = ActualPrimePowerError.error n := by
  unfold higherPowerError ActualPrimePowerError.error
  rw [psi_eq_chebyshev, theta_eq_chebyshev]

/-- The exact error from the signed prime-only reduction is unconditionally
square summable in the actual Pareto weight. -/
theorem summable_higherPowerError_energy :
    Summable (fun n : ℕ => weight n * higherPowerError n ^ 2) := by
  apply ActualPrimePowerError.summable_error_energy.congr
  intro n
  rw [higherPowerError_eq_actual_error]
  unfold weight
  ring

end RiemannResearch.RH.PrimeOnlyDyadicEnergy
