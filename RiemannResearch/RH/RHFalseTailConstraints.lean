import RiemannResearch.RH.CanonicalTailCapacityGeometry
import RiemannResearch.RH.TailCertificateCancellationEndpoint
import RiemannResearch.RH.ParetoPrimitiveRegularity
import RiemannResearch.RH.TwoSeedHeadEnergyGeometry
import RiemannResearch.RH.ChebyshevMellinRH

/-!
# Joint constraints forced by failure of the actual Riemann hypothesis

Source: user-provided RH-equivalence audit and first-coordinate/tail-capacity
continuation, 2026-09-19. This module assembles unconditional implications
under the single hypothesis `¬ RiemannHypothesis`. It does not use
PositiveResidueDensityFromRH and does not assume or assert RH.
The pole and polynomial lower bound come from existing actual Mellin theorems.
Canonical tail regularity and cofinal excursions specialize proved certificate
exclusion theorems. These constraints have not been shown contradictory.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity

theorem not_RH_pointDualResidual_ne_zero (hRH : ¬ RiemannHypothesis) :
    pointDualResidual ≠ 0 := by
  intro hr
  exact hRH (riemannHypothesis_of_canonicalTailSummability
    (canonicalTailSummability_iff_pointDualResidual_eq_zero.mpr hr))

/-- A single canonical object simultaneously satisfies the reciprocal residue
equations, a finite capacity limit, square-summable primitives, and failure of
both stronger cancellation conditions. No converse-from-RH provider is used. -/
theorem not_RH_canonical_obstruction (hRH : ¬ RiemannHypothesis) :
    IsResidueTailCertificate canonicalTailCertificate ∧
    Tendsto tailCapacity atTop (𝓝 (‖canonicalTailCertificate‖ ^ 2)) ∧
    Summable (fun n =>
      anchoredSignedTail (hilbertSequence canonicalTailCertificate) n ^ 2) ∧
    ¬ Summable (anchoredSignedTail (hilbertSequence canonicalTailCertificate)) ∧
    ¬ Summable (fun n : ℕ =>
      |additivePartialSum (hilbertSequence canonicalTailCertificate) n| / (n : ℝ)^2) := by
  have hr := not_RH_pointDualResidual_ne_zero hRH
  have hc := canonicalTailCertificate_isCertificate hr
  exact ⟨hc, tailCapacity_tendsto_canonical_energy hr,
    anchoredSignedTail_square_summable
      (hilbertSequence_square_summable canonicalTailCertificate),
    tailCertificate_not_summable_signedTail _ hc,
    tailCertificate_not_summable_partialSum_div_square _ hc⟩

/-- Every tail contains both signs of the same canonical certificate. -/
theorem not_RH_canonical_both_signs (hRH : ¬ RiemannHypothesis) (N : ℕ) :
    (∃ k, N ≤ k ∧ 2 ≤ k ∧ 0 < hilbertSequence canonicalTailCertificate k) ∧
    (∃ k, N ≤ k ∧ 2 ≤ k ∧ hilbertSequence canonicalTailCertificate k < 0) :=
  tailCertificate_both_signs_arbitrarily_far _ (not_RH_canonical_obstruction hRH).1 N

/-- Failure of RH forces arbitrarily late violations of every stated
sublinear power bound on the canonical signed partial sums. -/
theorem not_RH_canonical_power_excursions (hRH : ¬ RiemannHypothesis)
    (η : ℝ) (hη : 0 < η) (C : ℝ) (N : ℕ) :
    ∃ n, N ≤ n ∧ C * (n : ℝ) ^ (1 - η) <
      |additivePartialSum (hilbertSequence canonicalTailCertificate) n| := by
  by_contra! h
  apply tailCertificate_no_eventual_power_saving _
    (not_RH_canonical_obstruction hRH).1 hη
  filter_upwards [eventually_ge_atTop N] with n hn
  exact h n hn

/-- A logarithmic saving already fails cofinally, for every constant. -/
theorem not_RH_canonical_log_excursions (hRH : ¬ RiemannHypothesis)
    (η : ℝ) (hη : 0 < η) (C : ℝ) (N : ℕ) :
    ∃ n, N ≤ n ∧ C * (n : ℝ) / Real.log (2 * (n : ℝ)) ^ (1 + η) <
      |additivePartialSum (hilbertSequence canonicalTailCertificate) n| := by
  by_contra! h
  apply tailCertificate_no_eventual_log_saving _
    (not_RH_canonical_obstruction hRH).1 hη
  filter_upwards [eventually_ge_atTop N] with n hn
  exact h n hn

/-- The total accumulated capacity improvement has a finite exact limit.
Individual positive improvements therefore do not suffice for a contradiction. -/
theorem not_RH_accumulated_capacity_gain (hRH : ¬ RiemannHypothesis) :
    Tendsto (fun N => ∑ n ∈ Finset.range N,
      (tailCapacity (n + 1) - tailCapacity n)) atTop
      (𝓝 (‖canonicalTailCertificate‖ ^ 2 - tailCapacity 0)) := by
  have he (N : ℕ) : (∑ n ∈ Finset.range N,
      (tailCapacity (n + 1) - tailCapacity n)) = tailCapacity N - tailCapacity 0 := by
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ, ih]; ring
  simpa only [he] using (tailCapacity_tendsto_canonical_energy
    (not_RH_pointDualResidual_ne_zero hRH)).sub_const (tailCapacity 0)

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity

namespace RiemannResearch.RH.Pareto.CoefficientStabilization

/-- The limiting residual has a strictly positive first coordinate, and at
least one genuinely stabilized coefficient differs from the Möbius target. -/
theorem not_RH_first_coordinate_and_coefficient (hRH : ¬ RiemannHypothesis) :
    0 < hilbertSequence limitResidual 1 ∧
    ∃ m : ℕ, 1 < m ∧ limitCoefficient m ≠ -(ArithmeticFunction.moebius m : ℝ) := by
  have hn : hilbertSequence limitResidual 1 ≠ 0 :=
    fun h => hRH (riemannHypothesis_of_firstCoordinate_zero h)
  constructor
  · exact lt_of_le_of_ne firstCoordinate_nonneg (Ne.symm hn)
  · by_contra! h
    exact hRH (riemannHypothesis_of_limitCoefficients h)

end RiemannResearch.RH.Pareto.CoefficientStabilization

namespace RiemannResearch.RH.Pareto.TwoSeedExactHeadEnergy

/-- The full oscillatory Mellin lower bound passes to the actual unrestricted
finite-budget infimum. The compulsory head and complex phase remain present. -/
theorem energy_exact_lower_of_zeta
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) (N : ℕ) :
    (N : ℝ) / ((N : ℝ) + 1) +
      ((2 * s.re - 1) * ((N : ℝ) + 1) ^ (2 * s.re - 1) / ‖s‖ ^ 2) *
        ‖1 - ((N : ℂ) + 1)^(-s)‖ ^ 2 ≤ energy N := by
  apply le_energy
  intro f hf
  apply paretoMellin_exact_head_lower_bound hf.2 s hs
  apply paretoMellin_zero_on_legalClosure_of_zeta ({2, 3} : Set ℕ) _ s hs hs1 hz
    (Submodule.le_topologicalClosure _ hf.1)
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl <;> omega

/-- One and the same right-half-strip zero forces a genuine Mellin pole and
a fixed positive-power energy barrier at every sufficiently long head. -/
theorem not_RH_zero_pole_and_energy (hRH : ¬ RiemannHypothesis) :
    ∃ s : ℂ, riemannZeta s = 0 ∧ (1 / 2 : ℝ) < s.re ∧ s.re < 1 ∧
      meromorphicOrderAt RiemannResearch.RH.ChebyshevMellin.meromorphicError s = -1 ∧
      (∀ N : ℕ, 3 ≤ N →
        ((2 * s.re - 1) / (4 * ‖s‖ ^ 2)) *
          ((N : ℝ) + 1) ^ (2 * s.re - 1) ≤ energy N) ∧
      (∀ N : ℕ,
        (N : ℝ) / ((N : ℝ) + 1) +
          ((2 * s.re - 1) * ((N : ℝ) + 1) ^ (2 * s.re - 1) / ‖s‖ ^ 2) *
            ‖1 - ((N : ℂ) + 1)^(-s)‖ ^ 2 ≤ energy N) := by
  obtain ⟨s, hz, hs, hslt⟩ := RiemannResearch.RH.exists_right_zero_of_not_RH hRH
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  have hs1 : s ≠ 1 := by intro he; simp [he] at hslt
  exact ⟨s, hz, hs, hslt,
    RiemannResearch.RH.ChebyshevMellin.meromorphicError_order_at_zero hs0 hs1 hz,
    fun _ hN => energy_power_lower_of_zeta s hs hs1 hz hN,
    energy_exact_lower_of_zeta s hs hs1 hz⟩

/-- Under failure of RH the actual optimal head energy diverges; it cannot
settle at any finite positive plateau. -/
theorem not_RH_energy_tendsto_atTop (hRH : ¬ RiemannHypothesis) :
    Tendsto energy atTop atTop := by
  have hb : ¬ BddAbove (Set.range energy) := by
    intro hb
    exact hRH (riemannHypothesis_of_twoSeed_closure
      (energy_bddAbove_iff_closure.mp hb))
  apply tendsto_atTop.mpr
  intro B
  obtain ⟨e, ⟨N, rfl⟩, hB⟩ := not_bddAbove_iff.mp hb B
  filter_upwards [eventually_ge_atTop N] with M hM
  exact hB.le.trans (energy_monotone hM)

end RiemannResearch.RH.Pareto.TwoSeedExactHeadEnergy
