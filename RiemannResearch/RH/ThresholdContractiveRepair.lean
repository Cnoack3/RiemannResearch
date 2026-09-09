import RiemannResearch.Analysis.ContractiveRepairClosure
import RiemannResearch.RH.ThresholdHilbertLegal
import RiemannResearch.RH.ThresholdHilbertMean

/-!
# Contractive repairs in the actual weighted legal Hilbert space

This specializes the exact orbit/closure equivalence to the existing legal
two-seed approximation spaces and the actual constant target. The operator
contraction is an explicit hypothesis. The separate classical connection
from this approximation problem to RH is not assumed as an axiom.
-/

open Filter
open scoped Topology

namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Weighted expectation as a genuine continuous linear functional. -/
def hilbertMeanContinuous : ThresholdHilbert →L[ℝ] ℝ := innerSL ℝ hilbertOne

theorem hilbertMeanContinuous_apply (f : ThresholdHilbert) :
    hilbertMeanContinuous f = paretoMean (hilbertSequence f) := by
  change inner ℝ hilbertOne f = _
  rw [real_inner_comm]
  exact hilbert_inner_one f

@[simp] theorem hilbertMeanContinuous_one : hilbertMeanContinuous hilbertOne = 1 := by
  change inner ℝ hilbertOne hilbertOne = 1
  rw [real_inner_self_eq_norm_sq, hilbertOne_norm_sq]

theorem hilbertMeanContinuous_norm : ‖hilbertMeanContinuous‖ = 1 := by
  rw [hilbertMeanContinuous, innerSL_apply_norm]
  have hs := hilbertOne_norm_sq
  have hn := norm_nonneg hilbertOne
  nlinarith

/-- The centered Hilbert norm is exactly the complete weighted error from the
report; the anchored coordinate zero contributes zero. -/
theorem hilbert_error_weighted (f : ThresholdHilbert) :
    ‖f - hilbertOne‖ ^ 2 =
      ∑' k, positiveWeight k * (1 - hilbertSequence f k) ^ 2 := by
  rw [hilbert_norm_weighted_sq]
  apply tsum_congr
  intro k
  have hs := congrFun (hilbertSequenceLinear.map_sub f hilbertOne) k
  change hilbertSequence (f - hilbertOne) k =
    hilbertSequence f k - hilbertSequence hilbertOne k at hs
  rw [hs, hilbertOne_sequence]
  by_cases hk : k = 0
  · subst k
    norm_num [positiveWeight, zeroAnchor]
  · simp only [zeroAnchor, if_neg hk]
    ring

theorem weighted_error_tendsto_zero_of_hilbert_tendsto
    (F : ℕ → ThresholdHilbert) (hF : Tendsto F atTop (𝓝 hilbertOne)) :
    Tendsto (fun n => ∑' k, positiveWeight k * (1 - hilbertSequence (F n) k) ^ 2)
      atTop (𝓝 0) := by
  have hn := (tendsto_iff_norm_sub_tendsto_zero.1 hF).pow 2
  simpa only [hilbert_error_weighted, zero_pow (by norm_num : 2 ≠ 0)] using hn

/-- Any seed set, with every positive integer dilation retained: existence of
a finite legal repaired orbit is exactly target membership in the actual
closed legal space, provided the centered operator is a strict contraction. -/
theorem threshold_vanishing_repair_orbit_iff_legalClosure
    (A : Set ℕ) (P : ThresholdHilbert →L[ℝ] ThresholdHilbert) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hfix : P hilbertOne = hilbertOne)
    (hcontract : ∀ x, hilbertMeanContinuous x = 0 → ‖P x‖ ≤ q * ‖x‖) :
    Analysis.ContractiveRepair.HasVanishingRepairOrbit
      (hilbertLegalSubspace A) P hilbertMeanContinuous ↔
        hilbertOne ∈ hilbertLegalClosure A := by
  exact Analysis.ContractiveRepair.vanishing_repair_orbit_iff_mem_closure
    (hilbertLegalSubspace A) P hilbertMeanContinuous hilbertOne
    hq0 hq1 hfix hilbertMeanContinuous_one hcontract

/-- The requested two-seed consumer, still with its spectral and repair
obligations transparent. -/
theorem twoSeed_vanishing_repair_orbit_iff_legalClosure
    (P : ThresholdHilbert →L[ℝ] ThresholdHilbert) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hfix : P hilbertOne = hilbertOne)
    (hcontract : ∀ x, hilbertMeanContinuous x = 0 → ‖P x‖ ≤ q * ‖x‖) :
    Analysis.ContractiveRepair.HasVanishingRepairOrbit
      (hilbertLegalSubspace {2, 3}) P hilbertMeanContinuous ↔
        hilbertOne ∈ hilbertLegalClosure {2, 3} :=
  threshold_vanishing_repair_orbit_iff_legalClosure {2, 3} P hq0 hq1 hfix hcontract

end
end RiemannResearch.RH.Pareto
