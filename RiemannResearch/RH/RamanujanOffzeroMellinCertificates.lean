import RiemannResearch.RH.RamanujanMellinSignature
import RiemannResearch.RH.ParetoMellinSourcePerturbation
import RiemannResearch.RH.RamanujanMellinProduct
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Arithmetic Mellin certificates away from exact zeros

Source: the user's fourth Ramanujan transfer program, October 2026.
The regularized conductor correction is defined also at s=1. The exact probe
identities retain the signed cross term, complete correction capacity, full
Mellin integral, and full packet Gram excess. Approximate-zero bounds are
corollaries with explicit zeta-value budgets; no exact or approximate zero is
assumed to exist.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace RiemannResearch.RH.RamanujanZeroCertificates
open Pareto Pareto.CoefficientStabilization RamanujanCanonicalOptimizer
open RamanujanMellinSignature

/-- The actual packet transform, represented by its pole-removed arithmetic sum. -/
def packetMellinCorrection (n : ℕ) (a : Fin n → ℝ) (s : ℂ) : ℂ :=
  packetConductorSum n a s / s

def canonicalMellinCorrection (n : ℕ) (s : ℂ) : ℂ :=
  packetMellinCorrection n (packetCoefficients n) s

/-- At the removable point the arithmetic correction is exactly captured mass. -/
theorem canonicalMellinCorrection_one (n : ℕ) :
    canonicalMellinCorrection n 1 = (packetMass n : ℂ) := by
  simp only [canonicalMellinCorrection, packetMellinCorrection,
    packetConductorSum_one, div_one, packetMass]

theorem packetMellinCorrection_eq_zeta (n : ℕ) (a : Fin n → ℝ) (s : ℂ)
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    packetMellinCorrection n a s =
      riemannZeta s / s * packetArithmeticSum n a s := by
  rw [packetMellinCorrection, ← paretoMellin_packetSynthesis_conductor n a s hs]
  exact paretoMellin_packetSynthesis_zeta n a s hs hs1

theorem paretoMellin_packet_error_signature (n : ℕ) (a : Fin n → ℝ)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    paretoMellin (hilbertOne - Fintype.linearCombination ℝ
      (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) a) s =
        1 / s - packetMellinCorrection n a s := by
  change (paretoMellinContinuous s hs) (hilbertOne - _) = _
  rw [map_sub]
  change paretoMellin hilbertOne s - paretoMellin _ s = _
  rw [paretoMellin_one s hs,
    paretoMellin_packetSynthesis_conductor n a s (by linarith)]
  rfl

theorem paretoMellin_packetCandidate_error_signature (n : ℕ)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    paretoMellin (hilbertOne - packetCandidate n) s =
      1 / s - canonicalMellinCorrection n s :=
  paretoMellin_packet_error_signature n (packetCoefficients n) s hs

/-- The one-probe floor retains the regularized signature also at s=1. -/
theorem packet_regularized_single_probe_floor (n : ℕ) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) :
    (2 * s.re - 1) * ‖1 / s - canonicalMellinCorrection n s‖ ^ 2 ≤
      1 - packetMass n := by
  have h := paretoMellin_norm_sq_le (hilbertOne - packetCandidate n) s hs
  rw [paretoMellin_packetCandidate_error_signature n s hs, packet_error] at h
  have hd : 0 < 2 * s.re - 1 := by linarith
  simpa only [mul_comm] using (le_div_iff₀ hd).mp h

/-- A concrete one-probe arithmetic obstruction, with no zero assumption. -/
theorem packet_arithmetic_single_probe_floor (n : ℕ) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) :
    (2 * s.re - 1) *
      ‖(1 - riemannZeta s * packetArithmeticSum n (packetCoefficients n) s) / s‖ ^ 2 ≤
        1 - packetMass n := by
  have h := packet_regularized_single_probe_floor n s hs
  have he : 1 / s - canonicalMellinCorrection n s =
      (1 - riemannZeta s * packetArithmeticSum n (packetCoefficients n) s) / s := by
    rw [canonicalMellinCorrection,
      packetMellinCorrection_eq_zeta n (packetCoefficients n) s (by linarith) hs1]
    ring
  rw [he] at h
  exact h

variable {ι : Type*} [Fintype ι]

/-- Arbitrary finite probes, including repeated or singular families, retain
the exact arithmetic correction to the zero-test charge. -/
theorem packet_probe_test_energy_exact (z c : ι → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (n : ℕ) :
    1 - packetMass n = zeroTestCharge z c -
      2 * (∑ i, starRingEnd ℂ (c i) * canonicalMellinCorrection n (z i)).re +
      ∫ x in Ioi (1 : ℝ),
        ‖mellinWeightedStep (hilbertOne - packetCandidate n) x -
          starRingEnd ℂ (finiteMellinKernel z c x)‖ ^ 2 := by
  have h := finiteMellinKernel_remainder (hilbertOne - packetCandidate n) z c hzre
  have hsig (i : ι) : paretoMellin (hilbertOne - packetCandidate n) (z i) =
      1 / z i - canonicalMellinCorrection n (z i) :=
    paretoMellin_packetCandidate_error_signature n (z i) (hzre i)
  simp_rw [hsig] at h
  rw [packet_error] at h
  simp only [mul_sub, Finset.sum_sub_distrib, Complex.sub_re] at h
  unfold zeroTestCharge
  linarith

/-- Exact optimized product certificate for arbitrary distinct probes, including s=1. -/
theorem packet_probe_product_energy_exact [DecidableEq ι] (z : ι → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z) (n : ℕ) :
    1 - packetMass n = 1 - mellinZeroProduct z -
      2 * mellinSourceCross z (fun i => 1 / z i)
        (fun i => canonicalMellinCorrection n (z i)) +
      mellinInverseCapacity z (fun i => canonicalMellinCorrection n (z i)) +
      ∫ x in Ioi (1 : ℝ),
        ‖mellinWeightedStep (hilbertOne - packetCandidate n) x -
          starRingEnd ℂ (finiteMellinKernel z
            (mellinInverseCoefficients z
              ((fun i => 1 / z i) - (fun i => canonicalMellinCorrection n (z i)))) x)‖ ^ 2 := by
  have hd := (mellinCauchyGram_det_ne_zero_iff_injective z hzre).mpr hinj
  have h := finiteMellinKernel_perturbed_inverse_completion
    (hilbertOne - packetCandidate n) z (fun i => 1 / z i)
    (fun i => canonicalMellinCorrection n (z i)) hzre hd
    (fun i => paretoMellin_packetCandidate_error_signature n (z i) (hzre i))
  rw [packet_error, mellinInverseCapacity_zeroSource_product z hzre hinj] at h
  exact h

/-- Complete finite competitor identity: no Gram excess is discarded. -/
theorem packet_probe_product_completion [DecidableEq ι] (z : ι → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (n : ℕ) (a : Fin n → ℝ) :
    ‖hilbertOne - Fintype.linearCombination ℝ
      (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) a‖ ^ 2 =
      1 - mellinZeroProduct z -
      2 * mellinSourceCross z (fun i => 1 / z i)
        (fun i => canonicalMellinCorrection n (z i)) +
      mellinInverseCapacity z (fun i => canonicalMellinCorrection n (z i)) +
      (∫ x in Ioi (1 : ℝ),
        ‖mellinWeightedStep (hilbertOne - packetCandidate n) x -
          starRingEnd ℂ (finiteMellinKernel z
            (mellinInverseCoefficients z
              ((fun i => 1 / z i) - (fun i => canonicalMellinCorrection n (z i)))) x)‖ ^ 2) +
      ‖Fintype.linearCombination ℝ
        (fun i : Fin n => ramanujanPacketHilbert (i.val + 2))
        (a - packetCoefficients n)‖ ^ 2 := by
  rw [packet_completion, packet_probe_product_energy_exact z hzre hinj n]

theorem canonicalMellinCorrection_norm_le (n : ℕ) (s : ℂ) (ε : ℝ)
    (hs : 0 < s.re) (hs1 : s ≠ 1) (hζ : ‖riemannZeta s‖ ≤ ε) :
    ‖canonicalMellinCorrection n s‖ ≤
      ε / ‖s‖ * ‖packetArithmeticSum n (packetCoefficients n) s‖ := by
  rw [canonicalMellinCorrection,
    packetMellinCorrection_eq_zeta n (packetCoefficients n) s hs hs1,
    norm_mul, norm_div]
  exact mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hζ (norm_nonneg _)) (norm_nonneg _)

/-- Approximate-zero values bound the captured packet mass and the complete
correction capacity together. The zero assertion is replaced by a stated budget. -/
theorem packetMass_add_correctionCapacity_le_approximate_zeroProduct [DecidableEq ι]
    (z : ι → ℂ) (ε : ι → ℝ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (hz1 : ∀ i, z i ≠ 1) (hζ : ∀ i, ‖riemannZeta (z i)‖ ≤ ε i) (n : ℕ) :
    packetMass n + mellinInverseCapacity z
        (fun i => canonicalMellinCorrection n (z i)) ≤
      mellinZeroProduct z +
        2 * (∑ i, ‖mellinInverseCoefficients z (fun j => 1 / z j) i‖ *
          (ε i / ‖z i‖ * ‖packetArithmeticSum n (packetCoefficients n) (z i)‖)) := by
  have h := packet_probe_product_energy_exact z hzre hinj n
  have hc := mellinSourceCross_le_budget z (fun i => 1 / z i)
    (fun i => canonicalMellinCorrection n (z i))
    (fun i => ε i / ‖z i‖ * ‖packetArithmeticSum n (packetCoefficients n) (z i)‖)
    (fun i => canonicalMellinCorrection_norm_le n (z i) (ε i)
      (by linarith [hzre i]) (hz1 i) (hζ i))
  have hr : 0 ≤ ∫ x in Ioi (1 : ℝ),
      ‖mellinWeightedStep (hilbertOne - packetCandidate n) x -
        starRingEnd ℂ (finiteMellinKernel z
          (mellinInverseCoefficients z
            ((fun i => 1 / z i) - (fun i => canonicalMellinCorrection n (z i)))) x)‖ ^ 2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  linarith

end RiemannResearch.RH.RamanujanZeroCertificates
