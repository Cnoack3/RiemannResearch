import RiemannResearch.NumberTheory.PrimeNumberTheorem.LogarithmicMobiusConvolution
import RiemannResearch.NumberTheory.PrimeNumberTheorem.LogarithmicMobiusConvergence
import RiemannResearch.Analysis.LogarithmicAbelRemainder
import RiemannResearch.NumberTheory.PrimeNumberTheorem.PrimeErrorInverseLogFourth
import RiemannResearch.NumberTheory.PrimeNumberTheorem.MangoldtHarmonicAbel

/-!
# The classical logarithmic Möbius mean

Statement: NIST DLMF 27.11.15, https://dlmf.nist.gov/27.11.E15.
The arithmetic input is the repository's compatibility port of PNT+
MediumPNT (commit a5154676af9aa3095150ee410cdda80555aa0642), weakened to an
inverse-fourth-log estimate. Finite Abel and Dirichlet-convolution identities
then give the ordered logarithmic mean without a new Mertens hypothesis.

The intermediate theorem displays the harmonic-defect envelope explicitly;
the following provider discharges it from the established quantitative PNT.
The final theorem has no additional arithmetic hypotheses. This classical
result closes the constant source in `RH/NaturalMobiusSourceLimits`.
It does not assert RH, and no mathematical novelty is claimed.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.NumberTheory.PrimeNumberTheorem
open RiemannResearch.RH.Pareto

theorem logarithmicMobiusMean_tendsto_of_mangoldtHarmonicDefect_bound
    (β D : ℝ) (hD : 0 ≤ D)
    (hrem : ∀ q, 0 < q →
      |mangoldtHarmonicDefect q - β| ≤
        D / (1 + Real.log ((q : ℝ) + 1)) ^ 3) :
    Tendsto logarithmicMobiusMean atTop (𝓝 (-1 : ℝ)) := by
  have he := mobius_log_cube_quotient_convolution_tendsto_zero
    (fun q => mangoldtHarmonicDefect q - β) D hD hrem
  have hm := (mobiusReciprocalSum_tendsto_zero.const_mul (-β)).sub he
  have ht : Tendsto (fun N =>
      -β * mobiusReciprocalSum N -
        (∑ d ∈ Finset.Icc 1 N,
          ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) *
            (mangoldtHarmonicDefect (N / d) - β)) - 1)
      atTop (𝓝 (-1 : ℝ)) := by
    simpa only [mul_zero, sub_zero, zero_sub] using hm.sub_const 1
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have h := logarithmicMobiusMean_remainder_identity β N hN
  linarith

/-- The actual von-Mangoldt harmonic defect has a constant limiting value and
an unconditional inverse-cube-log remainder. The constant need not be
identified to obtain the logarithmic Möbius mean. -/
theorem mangoldtHarmonicDefect_inverse_log_cube_bound :
    ∃ β D : ℝ, 0 ≤ D ∧ ∀ q, 0 < q →
      |mangoldtHarmonicDefect q - β| ≤
        D / (1 + Real.log ((q : ℝ) + 1)) ^ 3 := by
  obtain ⟨C, hC, hR⟩ := R_inverseLogFourth_bound
  have hA : ∀ n : ℕ, 0 < n →
      |R (n : ℝ)| ≤ C * (n : ℝ) / (1 + Real.log n) ^ 4 := by
    intro n hn
    exact hR n (by exact_mod_cast hn)
  obtain ⟨β, hβ⟩ := RiemannResearch.Analysis.reciprocal_abel_inverse_log_remainder
    (fun n => R (n : ℝ)) C hC.le hA
  refine ⟨β, 32 * C, by positivity, ?_⟩
  intro q hq
  rw [mangoldtHarmonicDefect_eq_reciprocal_abel]
  simpa only [Nat.cast_add, Nat.cast_one] using hβ q hq

/-- The actual, ordered logarithmic reciprocal Möbius sums tend to minus one,
with no unproved arithmetic or RH premise. -/
theorem logarithmicMobiusMean_tendsto_neg_one :
    Tendsto logarithmicMobiusMean atTop (𝓝 (-1 : ℝ)) := by
  obtain ⟨β, D, hD, hrem⟩ := mangoldtHarmonicDefect_inverse_log_cube_bound
  exact logarithmicMobiusMean_tendsto_of_mangoldtHarmonicDefect_bound β D hD hrem

end RiemannResearch.NumberTheory.PrimeNumberTheorem
