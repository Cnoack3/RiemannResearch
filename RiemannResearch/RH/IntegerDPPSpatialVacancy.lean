import RiemannResearch.RH.IntegerDPPCoupling
import RiemannResearch.RH.IntegerDPPWeightedHoles

/-!
# All-site never-entry probabilities and the weighted RH criterion

Source: user-requested interpretation of spatial coupling, using the existing
arithmetic all-site Mellin obstruction. A supplied coupling realizes the
limiting hole probabilities as never-entry events. Their weighted summability
is exactly the existing arithmetic hypothesis, independent of coupling choice.
No spatial-coupling provider or summability estimate is assumed implicitly.
-/

noncomputable section
open MeasureTheory

namespace RiemannResearch.RH.Pareto.IntegerDPP
open RiemannResearch.Probability.DPP
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → Set ℕ)
    (hZ : ∀ n, IsDPP μ (Z n) (integerKernel n))
    (hmono : ∀ n ω, Z n ω ⊆ Z (n+1) ω)
include hZ hmono
theorem never_enter_site_probability (k : ℕ) :
    μ.real {ω | ∀ n, k ∉ Z n ω} = 1 - limitingKernel k k := by
  simpa [increasingUnion] using (increasingUnion_isDPP Z hZ hmono).vacancy k
theorem weighted_never_entry_summable_iff :
    Summable (fun k : ℕ => ((k : ℝ) + 1) * μ.real {ω | ∀ n, k ∉ Z n ω}) ↔
      Summable weightedLimitingHole := by
  change Summable _ ↔ Summable (fun k : ℕ => ((k : ℝ) + 1) * (1 - limitingKernel k k))
  simp only [never_enter_site_probability Z hZ hmono]
theorem riemannHypothesis_of_weighted_never_entry_summable
    (h : Summable (fun k : ℕ => ((k : ℝ) + 1) * μ.real {ω | ∀ n, k ∉ Z n ω})) :
    RiemannHypothesis :=
  riemannHypothesis_of_weightedLimitingHole_summable
    ((weighted_never_entry_summable_iff Z hZ hmono).mp h)
theorem weighted_never_entry_not_summable_of_not_RH (h : ¬ RiemannHypothesis) :
    ¬ Summable (fun k : ℕ => ((k : ℝ) + 1) * μ.real {ω | ∀ n, k ∉ Z n ω}) :=
  fun hs => h (riemannHypothesis_of_weighted_never_entry_summable Z hZ hmono hs)
theorem weighted_never_entry_harmonic_lower
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (h1 : s.re < 1) (hz : riemannZeta s = 0)
    (k : ℕ) :
    mellinHoleMassConstant s / ((k : ℝ) + 2) ≤
      ((k : ℝ) + 1) * μ.real {ω | ∀ n, k ∉ Z n ω} := by
  rw [never_enter_site_probability Z hZ hmono k]
  exact weightedLimitingHole_harmonic_lower s hs h1 hz k
end RiemannResearch.RH.Pareto.IntegerDPP

namespace RiemannResearch.RH.Pareto.IntegerDPP
/-- The same weighted criterion already has an unconditional marginal-law
interpretation; spatial coupling does not strengthen its numeric hypothesis. -/
theorem limitingLaw_weighted_hole_summable_iff :
    Summable (fun k : ℕ => ((k : ℝ) + 1) *
      limitingLaw.real {ω | ω k = false}) ↔ Summable weightedLimitingHole := by
  change Summable _ ↔ Summable (fun k : ℕ => ((k : ℝ) + 1) * (1 - limitingKernel k k))
  have hv (k : ℕ) : limitingLaw.real {ω | ω k = false} = 1 - limitingKernel k k := by
    simpa using limitingLaw_isDPP.vacancy k
  simp only [hv]
end RiemannResearch.RH.Pareto.IntegerDPP
