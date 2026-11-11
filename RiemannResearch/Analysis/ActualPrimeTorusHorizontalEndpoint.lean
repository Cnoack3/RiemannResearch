/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualRationalHorizontalEndpoint
import RiemannResearch.Analysis.ArithmeticWeightedFourierEndpoint
import RiemannResearch.Analysis.ActualPrimeTorusFMZRate

/-!
# Actual prime-torus endpoint and stronger-weight uniformity

Source: Sections 6--7 of `FRZ_Strengthening_2026-11-10.pdf`. The arithmetic
prime modes are actual rational modes. The endpoint therefore applies to
all fixed squared-height summable prime Fourier expansions. Uniformity is
proved on stronger weighted balls under the exact finite-tail condition.
The sole analytic provider remains `UniformSelbergDensity (1 / 4)`.
-/

noncomputable section
open Filter Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ActualPrimeTorusFMZ
open ActualZeroOrdinate PrimePhaseTorus PrimeTorusHaar

/-- The signed second-moment-corrected rational Fourier expansion associated
to the actual prime orbit is little-oh at the T/log T scale. -/
theorem tendsto_prime_correctedFourier_endpoint {ι : Type*}
    (P : Finset ℕ) (c : ι → ℂ) (k : ι → ℕ → ℤ)
    (hP : ∀ p ∈ P, p.Prime)
    (hc : Summable (fun i => ‖c i‖ * primeModeWeight P (k i) ^ 2))
    (hD : UniformSelbergDensity (1 / 4)) :
    Tendsto (fun T : ℝ => (Real.log T : ℂ) * ∑' i, c i *
      correctedRationalRemainder T (primeNumerator P (k i))
        (primeDenominator P (k i))) atTop (𝓝 0) := by
  exact tendsto_correctedRationalFourier_endpoint c
    (fun i => primeNumerator P (k i)) (fun i => primeDenominator P (k i))
    (fun i => primeProduct_pos P (fun p => (k i p).toNat) hP)
    (fun i => primeProduct_pos P (fun p => (-k i p).toNat) hP) hc hD

/-- Uniformity on any strengthened Fourier ball with a vanishing finite-tail
weight quotient. This includes arbitrarily slowly diverging improvements of
A₂, whenever the fixed prime-mode height has finite sublevel sets. -/
theorem eventually_uniform_prime_correctedFourier {ι : Type*}
    (P : Finset ℕ) (k : ι → ℕ → ℤ) (v : ι → ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hv : ∀ i, 0 < v i)
    (htail : ∀ η : ℝ, 0 < η → ∃ F : Finset ι,
      ∀ i ∉ F, primeModeWeight P (k i) ^ 2 ≤ η * v i)
    (hD : UniformSelbergDensity (1 / 4)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ c : ι → ℂ,
      Summable (fun i => ‖c i‖ * v i) → Fourier.weightedFourierMass c v ≤ 1 →
      ‖(Real.log T : ℂ) * ∑' i, c i *
        correctedRationalRemainder T (primeNumerator P (k i))
          (primeDenominator P (k i))‖ ≤ ε := by
  obtain ⟨C, hC, hb⟩ := eventually_log_mul_correctedRationalRemainder_le hD
  have hn : ∀ i, 1 ≤ primeNumerator P (k i) :=
    fun i => primeProduct_pos P (fun p => (k i p).toNat) hP
  have hm : ∀ i, 1 ≤ primeDenominator P (k i) :=
    fun i => primeProduct_pos P (fun p => (-k i p).toNat) hP
  have h := Fourier.eventually_uniform_weightedFourier_unitBall
    (fun T i => (Real.log T : ℂ) * correctedRationalRemainder T
      (primeNumerator P (k i)) (primeDenominator P (k i)))
    (fun i => primeModeWeight P (k i) ^ 2) v C hC hv
    (fun i => tendsto_log_mul_correctedRationalRemainder (hn i) (hm i)
      (1 / 4) (by norm_num) hD)
    (hb.mono (fun T hT i => hT _ _ (hn i) (hm i))) htail ε hε
  filter_upwards [h] with T hT
  intro c hc hmass
  have hh := hT c hc hmass
  convert hh using 1
  congr 1
  rw [Fourier.weightedFourierPairing, ← tsum_mul_left]
  apply tsum_congr
  intro i
  ring

end RiemannResearch.Analysis.ActualPrimeTorusFMZ
