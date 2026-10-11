import RiemannResearch.Analysis.ActualZeroOrdinate
import RiemannResearch.Analysis.BalancedTuplePhase
import RiemannResearch.Analysis.BalancedPowerTransfer

/-!
# Exact balanced phase hierarchy on the actual zeta-zero multiset

Source: user-supplied `Zeta_Zero_Harmonic_Analysis_20261011 (1)(1).md`,
Sections 5 and 9.5. The identities retain all ordered tuples and multiplicity
copies. An analytic entry-error estimate is explicit in the conditional
transfer theorem; no provider for that estimate is introduced here.

Recovery status, 2026-10-11: preserved Lean proof terms prepared for combined
integration; not yet certified by the final server checkpoint.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.ActualZeroOrdinate
open ZeroOrdinate BalancedTuplePhase BalancedPowerTransfer

/-- All balanced ordered tuples of actual zero copies, repetitions retained. -/
def ordinateBalancedSum (T u : ℝ) (r : ℕ) : ℂ :=
  balancedTupleSum r (fun c : Copies T => phase u (copyOrdinate T c))

theorem ordinateBalancedSum_eq_norm_pow (T u : ℝ) (r : ℕ) :
    ordinateBalancedSum T u r = ((‖ordinateSum T u‖ ^ (2 * r) : ℝ) : ℂ) := by
  unfold ordinateBalancedSum
  rw [balancedTupleSum_eq_norm_pow]
  have hs : ordinateSum T u =
      ∑ c : Copies T, phase u (copyOrdinate T c) :=
    sum_eq_copies T (fun ρ => phase u ρ.im)
  rw [← hs]

/-- Exact sharpening of the balanced coefficient-error transfer. The bound
on the actual Fourier coefficient remains a separate analytic hypothesis. -/
theorem balancedCoefficient_error_of_entry_bound
    (T u : ℝ) (b : ℂ) (e : ℝ) (he : 0 ≤ e)
    (hentry : ‖ordinateSum T u / (T : ℂ) - b‖ ≤ e) (r : ℕ) :
    |‖ordinateSum T u / (T : ℂ)‖ ^ (2 * r) - ‖b‖ ^ (2 * r)| ≤
      (‖b‖ + e) ^ (2 * r) - ‖b‖ ^ (2 * r) :=
  abs_norm_pow_sub_le_exact _ b e he hentry (2 * r)

end RiemannResearch.Analysis.ActualZeroOrdinate
