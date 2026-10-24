import RiemannResearch.RH.ParetoMellinInnovationRemainder
import RiemannResearch.RH.RamanujanOffzeroMellinCertificates

/-!
# Optimized arithmetic innovation at an arbitrary new Ramanujan Mellin probe

Source: the user's fifth Ramanujan transfer program, October 2026.
The poles are removed arithmetically, so the formulas include the point one.
No exact-zero hypothesis is required; all signature corrections, the signed
innovation cross term, and complete integral and competitor remainders remain.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace RiemannResearch.RH.RamanujanZeroCertificates
open Pareto RamanujanCanonicalOptimizer
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def packetMellinInnovation (n : ℕ) (z : ι → ℂ) (t : ℂ) : ℂ :=
  mellinSchurInnovation z (fun i => 1 / z i - canonicalMellinCorrection n (z i))
    t (1 / t - canonicalMellinCorrection n t)

theorem packetMellinInnovation_split (n : ℕ) (z : ι → ℂ) (t : ℂ) :
    packetMellinInnovation n z t =
      mellinSchurInnovation z (fun i => 1 / z i) t (1 / t) -
      mellinSchurInnovation z (fun i => canonicalMellinCorrection n (z i)) t
        (canonicalMellinCorrection n t) :=
  mellinSchurInnovation_sub_source z _ _ t _ _

theorem packetMellinInnovation_norm_sq (n : ℕ) (z : ι → ℂ) (t : ℂ) :
    ‖packetMellinInnovation n z t‖ ^ 2 =
      ‖mellinSchurInnovation z (fun i => 1 / z i) t (1 / t)‖ ^ 2 +
      ‖mellinSchurInnovation z (fun i => canonicalMellinCorrection n (z i)) t
        (canonicalMellinCorrection n t)‖ ^ 2 -
      2 * (mellinSchurInnovation z (fun i => 1 / z i) t (1 / t) * starRingEnd ℂ
        (mellinSchurInnovation z (fun i => canonicalMellinCorrection n (z i)) t
          (canonicalMellinCorrection n t))).re :=
  mellinSchurInnovation_sub_source_norm_sq z _ _ t _ _

theorem packet_probe_innovation_energy_exact (n : ℕ) (z : ι → ℂ) (t : ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (htre : (1 / 2 : ℝ) < t.re)
    (hinj : Function.Injective z) (hnew : ∀ i, z i ≠ t) :
    1 - packetMass n =
      mellinInverseCapacity z (fun i => 1 / z i - canonicalMellinCorrection n (z i)) +
      (2 * t.re - 1) * ‖packetMellinInnovation n z t‖ ^ 2 / mellinCenteredProduct z t +
      mellinProjectionRemainder (hilbertOne - packetCandidate n) (mellinAppend z t) := by
  have hd := (mellinCauchyGram_det_ne_zero_iff_injective z hzre).mpr hinj
  have h := finiteMellinKernel_inverse_completion (hilbertOne - packetCandidate n) z hzre hd
  change _ = _ + mellinProjectionRemainder (hilbertOne - packetCandidate n) z at h
  rw [mellinProjectionRemainder_append _ z t hzre htre hinj hnew, packet_error] at h
  have hsig (i : ι) : paretoMellin (hilbertOne - packetCandidate n) (z i) =
      1 / z i - canonicalMellinCorrection n (z i) :=
    paretoMellin_packetCandidate_error_signature n (z i) (hzre i)
  simp_rw [hsig, paretoMellin_packetCandidate_error_signature n t htre] at h
  simpa only [packetMellinInnovation, add_assoc] using h

theorem packet_probe_innovation_completion (n : ℕ) (a : Fin n → ℝ)
    (z : ι → ℂ) (t : ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (htre : (1 / 2 : ℝ) < t.re)
    (hinj : Function.Injective z) (hnew : ∀ i, z i ≠ t) :
    ‖hilbertOne - Fintype.linearCombination ℝ
      (fun j : Fin n => ramanujanPacketHilbert (j.val + 2)) a‖ ^ 2 =
      mellinInverseCapacity z (fun i => 1 / z i - canonicalMellinCorrection n (z i)) +
      (2 * t.re - 1) * ‖packetMellinInnovation n z t‖ ^ 2 / mellinCenteredProduct z t +
      mellinProjectionRemainder (hilbertOne - packetCandidate n) (mellinAppend z t) +
      ‖Fintype.linearCombination ℝ (fun j : Fin n => ramanujanPacketHilbert (j.val + 2))
        (a - packetCoefficients n)‖ ^ 2 := by
  rw [packet_completion, packet_probe_innovation_energy_exact n z t hzre htre hinj hnew]

theorem packet_probe_innovation_budget (n : ℕ) (z : ι → ℂ) (t : ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (htre : (1 / 2 : ℝ) < t.re)
    (hinj : Function.Injective z) (hnew : ∀ i, z i ≠ t) :
    (2 * t.re - 1) * ‖packetMellinInnovation n z t‖ ^ 2 ≤
      mellinCenteredProduct z t *
        (1 - packetMass n - mellinInverseCapacity z
          (fun i => 1 / z i - canonicalMellinCorrection n (z i))) := by
  have h := packet_probe_innovation_energy_exact n z t hzre htre hinj hnew
  have hr := mellinProjectionRemainder_nonneg (hilbertOne - packetCandidate n) (mellinAppend z t)
  have hp := mellinCenteredProduct_pos z t hzre htre hnew
  have hb : (2 * t.re - 1) * ‖packetMellinInnovation n z t‖ ^ 2 / mellinCenteredProduct z t ≤
      1 - packetMass n - mellinInverseCapacity z
        (fun i => 1 / z i - canonicalMellinCorrection n (z i)) := by linarith
  simpa only [mul_comm] using (div_le_iff₀ hp).mp hb

end RiemannResearch.RH.RamanujanZeroCertificates
