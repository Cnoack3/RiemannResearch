import RiemannResearch.RH.ParetoMellinSourceMetric
import RiemannResearch.RH.RamanujanOffzeroMellinCertificates

/-!
# Matrix-aware approximate-zero obstruction in actual Ramanujan coordinates

Source: the user's fifth Ramanujan transfer program, October 2026.
The complete arithmetic source correction is measured in the exact inverse
Mellin Gram metric. The existing signed product identity remains the primary
certificate; these bounds quantify how much approximate zero data can change it.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace RiemannResearch.RH.RamanujanZeroCertificates
open Pareto Pareto.CoefficientStabilization RamanujanCanonicalOptimizer
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem packet_probe_correction_metric_floor (z : ι → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z) (n : ℕ) :
    (Real.sqrt (1 - mellinZeroProduct z) -
      Real.sqrt (mellinInverseCapacity z (fun i => canonicalMellinCorrection n (z i)))) ^ 2 ≤
      1 - packetMass n := by
  have hd := (mellinCauchyGram_det_ne_zero_iff_injective z hzre).mpr hinj
  have h := finiteMellinKernel_source_metric_lower (hilbertOne - packetCandidate n) z
    (fun i => 1 / z i) (fun i => canonicalMellinCorrection n (z i)) hzre hd
    (fun i => paretoMellin_packetCandidate_error_signature n (z i) (hzre i))
  rwa [packet_error, mellinInverseCapacity_zeroSource_product z hzre hinj] at h

/-- The floor is useful with only an upper bound on the full correction capacity. -/
theorem packet_probe_correction_budget_floor (z : ι → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (n : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (he : mellinInverseCapacity z (fun i => canonicalMellinCorrection n (z i)) ≤ ε ^ 2) :
    (max 0 (Real.sqrt (1 - mellinZeroProduct z) - ε)) ^ 2 ≤ 1 - packetMass n := by
  have hd := (mellinCauchyGram_det_ne_zero_iff_injective z hzre).mpr hinj
  have he0 := mellinInverseCapacity_nonneg z
    (fun i => canonicalMellinCorrection n (z i)) hzre hd
  have hs := Real.sq_sqrt he0
  have hs0 := Real.sqrt_nonneg
    (mellinInverseCapacity z (fun i => canonicalMellinCorrection n (z i)))
  have hse : Real.sqrt (mellinInverseCapacity z
      (fun i => canonicalMellinCorrection n (z i))) ≤ ε := by nlinarith
  have h := packet_probe_correction_metric_floor z hzre hinj n
  by_cases hb : 0 ≤ Real.sqrt (1 - mellinZeroProduct z) - ε
  · rw [max_eq_right hb]
    have hp : 0 ≤ (ε - Real.sqrt (mellinInverseCapacity z
        (fun i => canonicalMellinCorrection n (z i)))) *
        (2 * Real.sqrt (1 - mellinZeroProduct z) - ε -
          Real.sqrt (mellinInverseCapacity z (fun i => canonicalMellinCorrection n (z i)))) :=
      mul_nonneg (sub_nonneg.mpr hse) (by linarith)
    nlinarith
  · rw [max_eq_left (le_of_not_ge hb)]
    simpa only [zero_pow (by decide : 2 ≠ 0)] using
      (show 0 ≤ 1 - packetMass n by rw [← packet_error]; positivity)

/-- A computed mass exceeding the robust floor certifies a violated correction budget. -/
theorem correctionCapacity_gt_of_packetMass_gt (z : ι → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (n : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hm : 1 - (max 0 (Real.sqrt (1 - mellinZeroProduct z) - ε)) ^ 2 < packetMass n) :
    ε ^ 2 < mellinInverseCapacity z (fun i => canonicalMellinCorrection n (z i)) := by
  by_contra he
  have h := packet_probe_correction_budget_floor z hzre hinj n ε hε (le_of_not_gt he)
  linarith

end RiemannResearch.RH.RamanujanZeroCertificates
