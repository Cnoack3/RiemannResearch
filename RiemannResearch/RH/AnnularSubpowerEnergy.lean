import RiemannResearch.Analysis.SubpowerPrefixMellin
import RiemannResearch.RH.AnnularEnergyRH

-- The private project has no Mathlib Apache license header. This scopes out
-- only that header-format check; theorem verification and other linters remain active.
set_option linter.style.header false in
/-!
# Subpower actual critical energy and off-line-zero growth

This strengthens the logarithmic sufficient hypothesis to eventual subpower
growth and records an exact characterization by all positive damping weights.
The prime/centered transfer retains the proved signed correction and square.
The subpower arithmetic estimate remains Open; RH is not established here.

Source: the classical weighted Mellin argument, assembled from the project's
actual Mellin identity and meromorphic continuation. NIST DLMF 2.5(i)
https://dlmf.nist.gov/2.5 supplies the general Mellin analyticity context,
not the actual arithmetic estimate.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace RiemannResearch.RH.AnnularSubpowerEnergy
open MeasureTheory.WeightedMellin
open RiemannResearch.Analysis.WeightedMellinTopology
open RiemannResearch.Analysis.SignedLatticeEnergy
open RiemannResearch.RH.AnnularPrimePair
open RiemannResearch.RH.AnnularCriticalEnergy
open RiemannResearch.RH.AnnularMellinContinuation
open RiemannResearch.RH.AnnularEnergyRH

/-- An eventual bound at every positive exponent; the constants and starting
cutoffs may depend on the exponent. This is an open arithmetic target. -/
def ActualPrimeSubpowerEnergy : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C X₀ : ℝ, ∀ X : ℝ, 1 ≤ X → X₀ ≤ X →
    criticalEnergy actualPrimeSignal X ≤ C * X ^ ε

def ActualCenteredSubpowerEnergy : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C X₀ : ℝ, ∀ X : ℝ, 1 ≤ X → X₀ ≤ X →
    actualIntegralEnergy X ≤ C * X ^ ε


theorem actualAnnular_Ha_of_eventual_power_energy {p a : ℝ}
    (hp : 0 ≤ p) (ha : (1 / 2 : ℝ) < a) (hpa : p < 2 * a - 1)
    (hbound : ∃ C X₀ : ℝ, ∀ X : ℝ, 1 ≤ X → X₀ ≤ X →
      criticalEnergy actualPrimeSignal X ≤ C * X ^ p) :
    Ha a actualAnnularVector := by
  obtain ⟨C, X₀, hC⟩ := hbound
  apply finiteEnergy_of_eventual_prefix_power actualAnnularVector
    actualAnnularVector_measurable actualAnnularVector_continuous.continuousOn
    C p (2 * a) hp (by linarith) hpa
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop X₀] with X hX hX₀
  rw [actualAnnular_prefix_eq_criticalEnergy hX]
  exact hC X hX hX₀

/-- Exact analytic characterization; neither side is an unconditional
arithmetic estimate. -/
theorem actualPrimeSubpowerEnergy_iff_all_damping :
    ActualPrimeSubpowerEnergy ↔
      ∀ a : ℝ, (1 / 2 : ℝ) < a → Ha a actualAnnularVector := by
  constructor
  · intro h a ha
    exact actualAnnular_Ha_of_eventual_power_energy
      (p := (2 * a - 1) / 2) (by linarith) ha (by linarith)
      (h _ (by linarith))
  · intro h ε hε
    refine ⟨energy actualAnnularVector (1 + ε), 1, ?_⟩
    intro X hX _
    have hf : FiniteEnergy actualAnnularVector (1 + ε) := by
      convert h ((1 + ε) / 2) (by linarith) using 1
      ring
    have hb := (finiteEnergy_prefix_rpow_le hf (u := 1) (by linarith) hX).2
    rw [show -(1 : ℝ) - 1 = -2 by norm_num,
      show (1 + ε) - 1 = ε by ring,
      actualAnnular_prefix_eq_criticalEnergy hX] at hb
    simpa only [mul_comm] using hb

/-- Conditional only on eventual subpower growth of the actual signal.
The logarithmic rate and separate analytic providers are unnecessary. -/
theorem riemannHypothesis_of_actualPrimeSubpowerEnergy
    (h : ActualPrimeSubpowerEnergy) : RiemannHypothesis :=
  riemannHypothesis_of_actualAnnular_all_damping
    (actualPrimeSubpowerEnergy_iff_all_damping.mp h)

theorem actualPrimeSubpowerEnergy_iff_actualCenteredSubpowerEnergy :
    ActualPrimeSubpowerEnergy ↔ ActualCenteredSubpowerEnergy := by
  constructor
  · intro h ε hε
    obtain ⟨C, X₀, hC⟩ := h ε hε
    refine ⟨C + 1105 / 5832, X₀, ?_⟩
    intro X hX hX₀
    have hd := (abs_le.mp (actualPrimeSignal_energy_difference_abs_le X)).1
    have hone := Real.one_le_rpow hX hε.le
    have hb := mul_le_mul_of_nonneg_left hone
      (by norm_num : (0 : ℝ) ≤ 1105 / 5832)
    nlinarith [hC X hX hX₀]
  · intro h ε hε
    obtain ⟨C, X₀, hC⟩ := h ε hε
    refine ⟨C + 1105 / 5832, X₀, ?_⟩
    intro X hX hX₀
    have hd := (abs_le.mp (actualPrimeSignal_energy_difference_abs_le X)).2
    have hone := Real.one_le_rpow hX hε.le
    have hb := mul_le_mul_of_nonneg_left hone
      (by norm_num : (0 : ℝ) ≤ 1105 / 5832)
    nlinarith [hC X hX hX₀]

theorem riemannHypothesis_of_actualCenteredSubpowerEnergy
    (h : ActualCenteredSubpowerEnergy) : RiemannHypothesis :=
  riemannHypothesis_of_actualPrimeSubpowerEnergy
    (actualPrimeSubpowerEnergy_iff_actualCenteredSubpowerEnergy.mpr h)

/-- A single eventual power bound excludes zeros past its precise exponent
threshold in the critical strip. -/
theorem zeta_ne_zero_of_actualPrime_eventual_power_energy {p : ℝ} {z : ℂ}
    (hp : 0 ≤ p) (hz1 : z.re < 1) (hpz : p < 2 * z.re - 1)
    (hbound : ∃ C X₀ : ℝ, ∀ X : ℝ, 1 ≤ X → X₀ ≤ X →
      criticalEnergy actualPrimeSignal X ≤ C * X ^ p) :
    riemannZeta z ≠ 0 := by
  let a : ℝ := ((p + 1) / 2 + z.re) / 2
  have ha : (1 / 2 : ℝ) < a := by dsimp [a]; linarith
  have hpa : p < 2 * a - 1 := by dsimp [a]; linarith
  have haz : a < z.re := by dsimp [a]; linarith
  have ha1 : a < 1 := haz.trans hz1
  have hzne : z ≠ 1 := by intro he; norm_num [he] at hz1
  exact zeta_ne_zero_of_actualAnnular_Ha (by linarith) ha1
    (actualAnnular_Ha_of_eventual_power_energy hp ha hpa hbound) haz hzne

/-- An off-line zero forces arbitrarily distant violations of every lower
power envelope; this is an all-cutoff asymptotic obstruction, not sampling. -/
theorem actualPrime_energy_cofinal_growth_of_zero {z : ℂ}
    (hz1 : z.re < 1)
    (hzero : riemannZeta z = 0) {p : ℝ}
    (hp : 0 ≤ p) (hpz : p < 2 * z.re - 1) (C X₀ : ℝ) :
    ∃ X : ℝ, max 2 X₀ ≤ X ∧ C * X ^ p < criticalEnergy actualPrimeSignal X := by
  by_contra! h
  exact zeta_ne_zero_of_actualPrime_eventual_power_energy hp hz1 hpz
    ⟨C, max 2 X₀, fun X _ hX => h X hX⟩ hzero

end RiemannResearch.RH.AnnularSubpowerEnergy
