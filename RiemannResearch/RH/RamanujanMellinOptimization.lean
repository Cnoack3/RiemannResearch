import RiemannResearch.RH.ParetoMellinGramOptimization
import RiemannResearch.RH.RamanujanZeroCertificates
import RiemannResearch.RH.RamanujanSaturationCriteria

/-! Exact optimized finite Mellin certificates for full Ramanujan errors.
Source: user-requested second transfer program, 23 October 2026. -/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.RamanujanZeroCertificates
open Pareto Pareto.CoefficientStabilization RamanujanCanonicalOptimizer
variable {ι : Type*} [Fintype ι]

/-- Every finite zero test loses exactly its complete Cauchy-Gram displacement
from any normal certificate, including when the Gram family is singular. -/
theorem packet_zeroTest_charge_completion (z c d : ι → ℂ)
    (hn : ∀ i, ∑ j, mellinCauchyGram z i j * d j = 1 / z i) :
    zeroTestCharge z d = zeroTestCharge z c +
      (mellinGramQuadratic z (c - d)).re :=
  mellinCharge_completion z (fun i => 1 / z i) c d hn

theorem packet_zeroTest_charge_maximal (z c d : ι → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re)
    (hn : ∀ i, ∑ j, mellinCauchyGram z i j * d j = 1 / z i) :
    zeroTestCharge z c ≤ zeroTestCharge z d :=
  mellinCharge_le_normal z (fun i => 1 / z i) c d hzre hn

/-- The optimized finite-zero inverse capacity, with its full Mellin remainder. -/
theorem packet_zeroInverse_energy_exact [DecidableEq ι]
    (z : ι → ℂ) (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0)
    (hdet : (mellinCauchyGram z).det ≠ 0) (n : ℕ) :
    1 - packetMass n = mellinInverseCapacity z (fun i => 1 / z i) +
      ∫ x in Ioi (1 : ℝ),
        ‖mellinWeightedStep (hilbertOne - packetCandidate n) x -
          starRingEnd ℂ (finiteMellinKernel z
            (mellinInverseCoefficients z (fun i => 1 / z i)) x)‖ ^ 2 := by
  have h := packet_zeroTest_energy_exact z
    (mellinInverseCoefficients z (fun i => 1 / z i)) hzre hz1 hzero n
  have hc := mellinCharge_inverse z (fun i => 1 / z i) hdet
  change zeroTestCharge z (mellinInverseCoefficients z (fun i => 1 / z i)) = _ at hc
  rwa [hc] at h

theorem packet_zeroInverse_completion [DecidableEq ι]
    (z : ι → ℂ) (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0)
    (hdet : (mellinCauchyGram z).det ≠ 0) (n : ℕ) (a : Fin n → ℝ) :
    ‖hilbertOne - Fintype.linearCombination ℝ
      (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) a‖ ^ 2 =
    mellinInverseCapacity z (fun i => 1 / z i) +
      (∫ x in Ioi (1 : ℝ),
        ‖mellinWeightedStep (hilbertOne - packetCandidate n) x -
          starRingEnd ℂ (finiteMellinKernel z
            (mellinInverseCoefficients z (fun i => 1 / z i)) x)‖ ^ 2) +
      ‖Fintype.linearCombination ℝ
        (fun i : Fin n => ramanujanPacketHilbert (i.val + 2))
        (a - packetCoefficients n)‖ ^ 2 := by
  rw [packet_completion, packet_zeroInverse_energy_exact z hzre hz1 hzero hdet n]

theorem zeroInverseCapacity_le_limitEnergy [DecidableEq ι]
    (z : ι → ℂ) (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0)
    (hdet : (mellinCauchyGram z).det ≠ 0) :
    mellinInverseCapacity z (fun i => 1 / z i) ≤ limitEnergy := by
  have h := zeroTestCharge_le_limitEnergy z
    (mellinInverseCoefficients z (fun i => 1 / z i)) hzre hz1 hzero
  have hc := mellinCharge_inverse z (fun i => 1 / z i) hdet
  change zeroTestCharge z (mellinInverseCoefficients z (fun i => 1 / z i)) = _ at hc
  rwa [hc] at h

end RiemannResearch.RH.RamanujanZeroCertificates
