import RiemannResearch.RH.QMellinTransfer
import RiemannResearch.RH.QRamanujanCanonicalOptimizer
import RiemannResearch.RH.RamanujanOffzeroMellinCertificates
import RiemannResearch.RH.ParetoMellinInnovationRemainder
import RiemannResearch.RH.ParetoMellinSourceMetric

/-!
# Complete-Q Ramanujan Mellin certificates with the exact measure correction

Source: the user's fifth Ramanujan transfer program, October 2026.
These certificates use the genuine Q inverse-Gram coefficients. Their full
Radon--Nikodym correction is retained alongside every signed arithmetic
correction, full Mellin integral, and full Q competitor excess.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace RiemannResearch.RH.QMellinTransfer
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer QParetoMetric
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Exact optimized finite-probe decomposition for every genuine Q vector. -/
theorem qMellin_inverse_capacity_completion (f : QHilbert) (z : ι → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z) :
    zetaTwo * ‖f‖ ^ 2 =
      mellinInverseCapacity z (fun i => qMellin f (z i)) +
      mellinProjectionRemainder (toPareto f) z + metricCorrection f := by
  rw [norm_identity]
  have h := finiteMellinKernel_inverse_completion (toPareto f) z hzre
    ((mellinCauchyGram_det_ne_zero_iff_injective z hzre).mpr hinj)
  change ‖toPareto f‖ ^ 2 = _ + mellinProjectionRemainder (toPareto f) z at h
  rw [h]
  rfl

theorem qMellin_source_metric_lower (f : QHilbert) (z b e : ι → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (hsig : ∀ i, qMellin f (z i) = b i - e i) :
    (Real.sqrt (mellinInverseCapacity z b) - Real.sqrt (mellinInverseCapacity z e)) ^ 2 +
      metricCorrection f ≤ zetaTwo * ‖f‖ ^ 2 := by
  rw [norm_identity]
  have h := finiteMellinKernel_source_metric_lower (toPareto f) z b e hzre
    ((mellinCauchyGram_det_ne_zero_iff_injective z hzre).mpr hinj) hsig
  linarith

end RiemannResearch.RH.QMellinTransfer

namespace RiemannResearch.RH.QRamanujanMellinCertificates
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer QParetoMetric
open QRamanujanCanonicalOptimizer QMellinTransfer RamanujanZeroCertificates
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def qCanonicalMellinCorrection (n : ℕ) (s : ℂ) : ℂ :=
  packetMellinCorrection n (QRamanujanCanonicalOptimizer.packetCoefficients n) s

theorem toPareto_finitePacketSynthesis (n : ℕ) (a : Fin n → ℝ) :
    toPareto (Fintype.linearCombination ℝ (packetFamily n) a) =
      Fintype.linearCombination ℝ (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) a := by
  change toParetoLinear (∑ i : Fin n, a i • QRamanujanPackets.qRamanujanPacket (i.val + 2)) = _
  simp only [map_sum, map_smul]
  change (∑ i : Fin n, a i • toPareto (QRamanujanPackets.qRamanujanPacket (i.val + 2))) = _
  simp only [RamanujanPrimeCoordinates.toPareto_packet]
  rfl

theorem qMellin_packet_error_signature (n : ℕ) (a : Fin n → ℝ) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) :
    qMellin (qOne - Fintype.linearCombination ℝ (packetFamily n) a) s =
      1 / s - packetMellinCorrection n a s := by
  have he : toPareto (qOne - Fintype.linearCombination ℝ (packetFamily n) a) =
      hilbertOne - Fintype.linearCombination ℝ
        (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) a := by
    change toParetoLinear (qOne - _) = _
    rw [map_sub]
    change toPareto qOne - toPareto _ = _
    rw [toPareto_qOne, toPareto_finitePacketSynthesis]
  rw [qMellin, he]
  exact paretoMellin_packet_error_signature n a s hs

theorem qMellin_packetCandidate_error_signature (n : ℕ) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) :
    qMellin (qOne - packetCandidate n) s = 1 / s - qCanonicalMellinCorrection n s :=
  qMellin_packet_error_signature n (packetCoefficients n) s hs

theorem qCanonicalMellinCorrection_eq_zeta (n : ℕ) (s : ℂ)
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    qCanonicalMellinCorrection n s = riemannZeta s / s *
      RamanujanMellinSignature.packetArithmeticSum n (packetCoefficients n) s :=
  packetMellinCorrection_eq_zeta n (packetCoefficients n) s hs hs1

/-- The exact Q analogue retains the full positive measure correction. -/
theorem qPacket_probe_product_energy_exact (z : ι → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z) (n : ℕ) :
    zetaTwo * (1 - packetMass n) = 1 - mellinZeroProduct z -
      2 * mellinSourceCross z (fun i => 1 / z i)
        (fun i => qCanonicalMellinCorrection n (z i)) +
      mellinInverseCapacity z (fun i => qCanonicalMellinCorrection n (z i)) +
      mellinProjectionRemainder (toPareto (qOne - packetCandidate n)) z +
      metricCorrection (qOne - packetCandidate n) := by
  have h := qMellin_inverse_capacity_completion (qOne - packetCandidate n) z hzre hinj
  have hsig (i : ι) : qMellin (qOne - packetCandidate n) (z i) =
      1 / z i - qCanonicalMellinCorrection n (z i) :=
    qMellin_packetCandidate_error_signature n (z i) (hzre i)
  simp_rw [hsig] at h
  have hc := mellinInverseCapacity_sub_source z (fun i => 1 / z i)
    (fun i => qCanonicalMellinCorrection n (z i))
    ((mellinCauchyGram_det_ne_zero_iff_injective z hzre).mpr hinj)
  change mellinInverseCapacity z
    (fun i => 1 / z i - qCanonicalMellinCorrection n (z i)) = _ at hc
  rw [packet_error, hc,
    mellinInverseCapacity_zeroSource_product z hzre hinj] at h
  exact h

theorem qPacket_probe_product_completion (z : ι → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (n : ℕ) (a : Fin n → ℝ) :
    zetaTwo * ‖qOne - Fintype.linearCombination ℝ (packetFamily n) a‖ ^ 2 =
      1 - mellinZeroProduct z -
      2 * mellinSourceCross z (fun i => 1 / z i)
        (fun i => qCanonicalMellinCorrection n (z i)) +
      mellinInverseCapacity z (fun i => qCanonicalMellinCorrection n (z i)) +
      mellinProjectionRemainder (toPareto (qOne - packetCandidate n)) z +
      metricCorrection (qOne - packetCandidate n) +
      zetaTwo * ‖Fintype.linearCombination ℝ (packetFamily n) (a - packetCoefficients n)‖ ^ 2 := by
  rw [packet_completion, mul_add, qPacket_probe_product_energy_exact z hzre hinj n]

theorem qPacket_probe_correction_metric_floor (z : ι → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z) (n : ℕ) :
    (Real.sqrt (1 - mellinZeroProduct z) -
      Real.sqrt (mellinInverseCapacity z (fun i => qCanonicalMellinCorrection n (z i)))) ^ 2 +
      metricCorrection (qOne - packetCandidate n) ≤ zetaTwo * (1 - packetMass n) := by
  have h := qMellin_source_metric_lower (qOne - packetCandidate n) z
    (fun i => 1 / z i) (fun i => qCanonicalMellinCorrection n (z i)) hzre hinj
    (fun i => qMellin_packetCandidate_error_signature n (z i) (hzre i))
  rwa [packet_error, mellinInverseCapacity_zeroSource_product z hzre hinj] at h

/-- Exact-zero product obstruction for the actual Q optimizer, with both full remainders. -/
theorem qPacket_zeroProduct_energy_exact (z : ι → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0) (n : ℕ) :
    zetaTwo * (1 - packetMass n) = 1 - mellinZeroProduct z +
      mellinProjectionRemainder (toPareto (qOne - packetCandidate n)) z +
      metricCorrection (qOne - packetCandidate n) := by
  have h := qMellin_inverse_capacity_completion (qOne - packetCandidate n) z hzre hinj
  have hsig (i : ι) : qMellin (qOne - packetCandidate n) (z i) = 1 / z i := by
    rw [qMellin_packetCandidate_error_signature n (z i) (hzre i),
      qCanonicalMellinCorrection_eq_zeta n (z i) (by linarith [hzre i]) (hz1 i),
      hzero i, zero_div, zero_mul, sub_zero]
  simp_rw [hsig] at h
  rwa [packet_error, mellinInverseCapacity_zeroSource_product z hzre hinj] at h

theorem qPacket_zeroProduct_mass_bound (z : ι → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0) (n : ℕ) :
    1 - zetaTwo * (1 - packetMass n) + metricCorrection (qOne - packetCandidate n) ≤
      mellinZeroProduct z := by
  have h := qPacket_zeroProduct_energy_exact z hzre hinj hz1 hzero n
  have hr := mellinProjectionRemainder_nonneg (toPareto (qOne - packetCandidate n)) z
  linarith

end RiemannResearch.RH.QRamanujanMellinCertificates
