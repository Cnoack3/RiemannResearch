import RiemannResearch.RH.ThresholdContractiveRepair
import RiemannResearch.RH.ParetoGibbsHilbert
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Actual Gibbs repair identities and the explicit spectral-gap interface

The Gibbs operator here is the concrete infinite operator already built on
the actual weighted Hilbert space. Exact energy identities are unconditional.
The convergence consumers retain `ParetoGibbsSharpGap` as an explicit reusable
input. `ParetoGibbsSpectralGap` supplies its proved unconditional provider and
exports the corresponding unconditional analytic consequences. Existence of
legal vanishing repairs remains the open arithmetic construction problem.
-/

open Filter
open scoped Topology

namespace RiemannResearch.RH.Pareto
noncomputable section

theorem hilbertGibbs_mean_continuous (f : ThresholdHilbert) :
    hilbertMeanContinuous (hilbertGibbs f) = hilbertMeanContinuous f := by
  change inner ℝ hilbertOne (hilbertGibbs f) = inner ℝ hilbertOne f
  calc
    inner ℝ hilbertOne (hilbertGibbs f) = inner ℝ (hilbertGibbs f) hilbertOne :=
      real_inner_comm _ _
    _ = inner ℝ f hilbertOne := hilbertGibbs_mean_inner f
    _ = inner ℝ hilbertOne f := real_inner_comm _ _

theorem sharpGap_centered_bound (hgap : ParetoGibbsSharpGap)
    (f : ThresholdHilbert) (hf : hilbertMeanContinuous f = 0) :
    ‖hilbertGibbsContinuous f‖ ≤ (Real.pi / 4) * ‖f‖ := by
  apply hgap f
  rw [← hilbertGibbs_inner_one]
  change inner ℝ hilbertOne f = 0 at hf
  rwa [real_inner_comm] at hf

/-- The complete actual one-step identity, including its signed cross term. -/
theorem hilbertGibbs_repair_energy (F : ℕ → ThresholdHilbert) (n : ℕ) :
    ‖F (n + 1) - hilbertOne‖ ^ 2 =
      ‖hilbertGibbs (F n - hilbertOne)‖ ^ 2 +
      2 * inner ℝ (hilbertGibbs (F n - hilbertOne))
        (Analysis.ContractiveRepair.repairError hilbertGibbsLinear F n) +
      ‖Analysis.ContractiveRepair.repairError hilbertGibbsLinear F n‖ ^ 2 := by
  have h := Analysis.ContractiveRepair.centered_recurrence
    hilbertGibbsLinear F hilbertOne hilbertGibbs_one n
  rw [h]
  exact norm_add_sq_real _ _

/-- Actual Gibbs dynamics: the contraction bound plus vanishing actual errors
implies convergence. `ParetoGibbsSpectralGap` supplies the contraction bound;
the existence of legal vanishing repairs is not asserted here. -/
theorem hilbertGibbs_tendsto_of_vanishing_repair
    (hgap : ParetoGibbsSharpGap) (F : ℕ → ThresholdHilbert)
    (hm : ∀ n, hilbertMeanContinuous (F n) = 1)
    (he : Tendsto (Analysis.ContractiveRepair.repairError hilbertGibbsLinear F)
      atTop (𝓝 0)) : Tendsto F atTop (𝓝 hilbertOne) := by
  exact Analysis.ContractiveRepair.tendsto_fixedPoint_of_vanishing_repair
    hilbertGibbsLinear hilbertMeanContinuous.toLinearMap F hilbertOne
    (by positivity : 0 ≤ Real.pi / 4)
    (by have h := Real.pi_lt_four; linarith : Real.pi / 4 < 1)
    hilbertGibbs_one hilbertMeanContinuous_one hm
    (sharpGap_centered_bound hgap) he

/-- Exact two-seed closure equivalence for the actual Gibbs operator, with the
sharp spectral theorem retained as an explicit hypothesis. -/
theorem hilbertGibbs_legal_repair_iff_closure (hgap : ParetoGibbsSharpGap) :
    Analysis.ContractiveRepair.HasVanishingRepairOrbit
      (hilbertLegalSubspace {2, 3}) hilbertGibbsContinuous hilbertMeanContinuous ↔
        hilbertOne ∈ hilbertLegalClosure {2, 3} := by
  exact twoSeed_vanishing_repair_orbit_iff_legalClosure hilbertGibbsContinuous
    (by positivity : 0 ≤ Real.pi / 4)
    (by have h := Real.pi_lt_four; linarith : Real.pi / 4 < 1)
    hilbertGibbs_one (sharpGap_centered_bound hgap)

end
end RiemannResearch.RH.Pareto
