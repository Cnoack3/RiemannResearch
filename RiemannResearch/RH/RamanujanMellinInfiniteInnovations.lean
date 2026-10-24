import RiemannResearch.RH.RamanujanMellinInnovationSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Complete infinite Mellin innovation accounting

Source: nonnegative Schur telescoping and the complete finite physical
identity, 24 October 2026. Innovation summability is unconditional for every
actual Hilbert vector. The limiting unobserved energy is retained explicitly;
no completeness of the chosen Mellin probes is assumed.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto

def mellinCapacityLimit (f : ThresholdHilbert) (z : ℕ → ℂ) : ℝ :=
  ∑' n, mellinPrefixInnovation z (fun j => paretoMellin f (z j)) n

def mellinUnobservedEnergy (f : ThresholdHilbert) (z : ℕ → ℂ) : ℝ :=
  ‖f‖ ^ 2 - mellinCapacityLimit f z

theorem mellinPhysicalInnovation_summable (f : ThresholdHilbert) (z : ℕ → ℂ)
    (hz : ∀ n, (1 / 2 : ℝ) < (z n).re) (hinj : Function.Injective z) :
    Summable (mellinPrefixInnovation z (fun j => paretoMellin f (z j))) := by
  apply summable_of_sum_range_le (c := ‖f‖ ^ 2) (mellinPrefixInnovation_nonneg z _ hz)
  intro N
  have he := mellinPrefixInnovation_physical_completion f z hz hinj N
  have hr := mellinProjectionRemainder_nonneg f (fun i : Fin N => z i.val)
  linarith

theorem mellinPrefixCapacity_physical_tendsto (f : ThresholdHilbert) (z : ℕ → ℂ)
    (hz : ∀ n, (1 / 2 : ℝ) < (z n).re) (hinj : Function.Injective z) :
    Tendsto (mellinPrefixCapacity z (fun j => paretoMellin f (z j)))
      atTop (𝓝 (mellinCapacityLimit f z)) := by
  simpa only [mellinPrefixInnovation_sum z _ hz hinj, mellinCapacityLimit] using
    (mellinPhysicalInnovation_summable f z hz hinj).hasSum.tendsto_sum_nat

theorem mellinCapacityLimit_bounds (f : ThresholdHilbert) (z : ℕ → ℂ)
    (hz : ∀ n, (1 / 2 : ℝ) < (z n).re) (hinj : Function.Injective z) :
    0 ≤ mellinCapacityLimit f z ∧ mellinCapacityLimit f z ≤ ‖f‖ ^ 2 := by
  constructor
  · exact tsum_nonneg (mellinPrefixInnovation_nonneg z _ hz)
  · apply le_of_tendsto' (mellinPrefixCapacity_physical_tendsto f z hz hinj)
    intro N
    have he := mellinPrefixInnovation_physical_completion f z hz hinj N
    rw [mellinPrefixInnovation_sum z _ hz hinj] at he
    have hr := mellinProjectionRemainder_nonneg f (fun i : Fin N => z i.val)
    linarith

theorem mellinUnobservedEnergy_nonneg (f : ThresholdHilbert) (z : ℕ → ℂ)
    (hz : ∀ n, (1 / 2 : ℝ) < (z n).re) (hinj : Function.Injective z) :
    0 ≤ mellinUnobservedEnergy f z :=
  sub_nonneg.mpr (mellinCapacityLimit_bounds f z hz hinj).2

/-- Exact infinite tail decomposition, including the unresolved unobserved energy. -/
theorem mellinProjectionRemainder_tail_exact (f : ThresholdHilbert) (z : ℕ → ℂ)
    (hz : ∀ n, (1 / 2 : ℝ) < (z n).re) (hinj : Function.Injective z) (N : ℕ) :
    mellinProjectionRemainder f (fun i : Fin N => z i.val) =
      (∑' n, mellinPrefixInnovation z (fun j => paretoMellin f (z j)) (n + N)) +
        mellinUnobservedEnergy f z := by
  have hs := (mellinPhysicalInnovation_summable f z hz hinj).sum_add_tsum_nat_add N
  have he := mellinPrefixInnovation_physical_completion f z hz hinj N
  unfold mellinUnobservedEnergy mellinCapacityLimit
  linarith

theorem mellinProjectionRemainder_prefix_tendsto (f : ThresholdHilbert) (z : ℕ → ℂ)
    (hz : ∀ n, (1 / 2 : ℝ) < (z n).re) (hinj : Function.Injective z) :
    Tendsto (fun N => mellinProjectionRemainder f (fun i : Fin N => z i.val))
      atTop (𝓝 (mellinUnobservedEnergy f z)) := by
  have ht : Tendsto (fun N => ‖f‖ ^ 2 -
      mellinPrefixCapacity z (fun j => paretoMellin f (z j)) N)
      atTop (𝓝 (‖f‖ ^ 2 - mellinCapacityLimit f z)) :=
    tendsto_const_nhds.sub (mellinPrefixCapacity_physical_tendsto f z hz hinj)
  have he (N : ℕ) : mellinProjectionRemainder f (fun i : Fin N => z i.val) =
      ‖f‖ ^ 2 - mellinPrefixCapacity z (fun j => paretoMellin f (z j)) N := by
    have h := mellinPrefixInnovation_physical_completion f z hz hinj N
    rw [mellinPrefixInnovation_sum z _ hz hinj] at h
    linarith
  simpa only [he, mellinUnobservedEnergy] using ht

theorem mellinProjectionRemainder_prefix_antitone (f : ThresholdHilbert) (z : ℕ → ℂ)
    (hz : ∀ n, (1 / 2 : ℝ) < (z n).re) (hinj : Function.Injective z) :
    Antitone (fun N => mellinProjectionRemainder f (fun i : Fin N => z i.val)) := by
  intro N M hNM
  have hc : (∑ n ∈ Finset.range N,
      mellinPrefixInnovation z (fun j => paretoMellin f (z j)) n) ≤
      ∑ n ∈ Finset.range M, mellinPrefixInnovation z (fun j => paretoMellin f (z j)) n :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hNM)
      (fun n _ _ => mellinPrefixInnovation_nonneg z _ hz n)
  have hN := mellinPrefixInnovation_physical_completion f z hz hinj N
  have hM := mellinPrefixInnovation_physical_completion f z hz hinj M
  linarith only [hN, hM, hc]

/-- Complete accounting is unconditional; identifying the final term with zero is separate. -/
theorem mellin_infinite_energy_exact (f : ThresholdHilbert) (z : ℕ → ℂ) :
    ‖f‖ ^ 2 = mellinCapacityLimit f z + mellinUnobservedEnergy f z := by
  unfold mellinUnobservedEnergy
  ring

theorem mellin_zero_iff_both_energies_zero (f : ThresholdHilbert) (z : ℕ → ℂ)
    (hz : ∀ n, (1 / 2 : ℝ) < (z n).re) (hinj : Function.Injective z) :
    f = 0 ↔ mellinCapacityLimit f z = 0 ∧ mellinUnobservedEnergy f z = 0 := by
  have hc := (mellinCapacityLimit_bounds f z hz hinj).1
  have hr := mellinUnobservedEnergy_nonneg f z hz hinj
  have he := mellin_infinite_energy_exact f z
  constructor
  · intro hf
    have hn : ‖f‖ ^ 2 = 0 := by rw [hf, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    constructor <;> linarith
  · rintro ⟨h₁, h₂⟩
    have hn : ‖f‖ ^ 2 = 0 := by linarith
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)

end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.QRamanujanMellinCertificates
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer QParetoMetric

theorem qMellin_infinite_energy_exact (f : QHilbert) (z : ℕ → ℂ) :
    zetaTwo * ‖f‖ ^ 2 = mellinCapacityLimit (toPareto f) z +
      mellinUnobservedEnergy (toPareto f) z + metricCorrection f := by
  rw [norm_identity, mellin_infinite_energy_exact (toPareto f) z]

end RiemannResearch.RH.QRamanujanMellinCertificates
