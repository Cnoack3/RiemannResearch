import RiemannResearch.RH.ChebyshevEnergyHardy
import RiemannResearch.RH.ChebyshevMellinRH

/-!
# Chebyshev poles and the failed-Hardy conditions

Source: user-provided stringent not-RH conditions, 2026-09-21, groups 28 and 29.
The pole and Hardy obstructions below concern the actual meromorphic Chebyshev
expression. They do not silently identify an otherwise divergent Bochner
integral with its analytic continuation. The endpoint energy divergence is
recorded as a precise OPEN target, not as an axiom or a proved consequence.
-/

noncomputable section
open MeasureTheory.WeightedMellin

namespace RiemannResearch.RH.ChebyshevMellin

/-- A genuine zero inside the Hardy half-plane prevents the actual
meromorphic expression from belonging to that Hardy space. -/
theorem meromorphicError_not_hardy_of_zero
    {ρ : ℂ} (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1)
    (hzero : riemannZeta ρ = 0) {α : ℝ} (hα : α < ρ.re) :
    ¬ HardyH2 meromorphicError α := by
  intro hhardy
  exact (analyticAt_meromorphicError_iff hρ0 hρ1).mp
    (hhardy.1 ρ hα) hzero

/-- The same off-line zero witnesses a simple meromorphic pole and failure of
every Hardy half-plane whose boundary lies strictly to its left. Multiplicity
does not change the order of the logarithmic-derivative pole. -/
theorem off_line_zero_pole_and_all_hardy_obstructions
    {ρ : ℂ} (hhalf : (1 / 2 : ℝ) < ρ.re) (hone : ρ.re < 1)
    (hzero : riemannZeta ρ = 0) :
    meromorphicOrderAt meromorphicError ρ = -1 ∧
      ∀ α : ℝ, α < ρ.re → ¬ HardyH2 meromorphicError α := by
  have hρ0 : ρ ≠ 0 := by
    intro h
    norm_num [h] at hhalf
  have hρ1 : ρ ≠ 1 := by
    intro h
    norm_num [h] at hone
  exact ⟨meromorphicError_order_at_zero hρ0 hρ1 hzero,
    fun _ hα => meromorphicError_not_hardy_of_zero hρ0 hρ1 hzero hα⟩

/-- Failed RH gives an actual right-half-strip zero with both analytic
obstructions, using the already proved RH/analyticity equivalence. -/
theorem not_RH_exists_chebyshev_pole_and_hardy_obstructions
    (hRH : ¬ RiemannHypothesis) :
    ∃ ρ : ℂ, (1 / 2 : ℝ) < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0 ∧
      meromorphicOrderAt meromorphicError ρ = -1 ∧
      ∀ α : ℝ, α < ρ.re → ¬ HardyH2 meromorphicError α := by
  classical
  have hnot : ¬ ∀ ρ : ℂ, (1 / 2 : ℝ) < ρ.re → ρ.re < 1 →
      AnalyticAt ℂ meromorphicError ρ :=
    fun h => hRH (riemannHypothesis_iff_error_analytic.mpr h)
  push Not at hnot
  obtain ⟨ρ, hhalf, hone, hbad⟩ := hnot
  have hρ0 : ρ ≠ 0 := by
    intro h
    norm_num [h] at hhalf
  have hρ1 : ρ ≠ 1 := by
    intro h
    norm_num [h] at hone
  have hzero : riemannZeta ρ = 0 := by
    by_contra hn
    exact hbad ((analyticAt_meromorphicError_iff hρ0 hρ1).mpr hn)
  exact ⟨ρ, hhalf, hone, hzero,
    off_line_zero_pole_and_all_hardy_obstructions hhalf hone hzero⟩

/-- OPEN analytic target: includes the endpoint epsilon = 2 Re(rho)-1.
`ErrorFiniteEnergy (1+epsilon)` uses the actual nonnegative integrand
(psi(x)-x)^2 x^(-2-epsilon); its negation avoids the totalized-integral trap.
The missing provider must establish analytic continuation and the boundary
pole obstruction at the endpoint, not merely interior holomorphy. -/
def OffLineZeroDampedEnergyDivergenceTarget : Prop :=
  ∀ ρ : ℂ, riemannZeta ρ = 0 → (1 / 2 : ℝ) < ρ.re → ρ.re < 1 →
    ∀ ε : ℝ, 0 < ε → ε ≤ 2 * ρ.re - 1 → ¬ ErrorFiniteEnergy (1 + ε)

end RiemannResearch.RH.ChebyshevMellin
