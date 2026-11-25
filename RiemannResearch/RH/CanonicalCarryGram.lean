import RiemannResearch.Analysis.HilbertConstraintEnergy
import RiemannResearch.Analysis.FiniteSingularGramReconstruction
import RiemannResearch.RH.MeanOneResidualFloor
import RiemannResearch.RH.NaturalMobiusSourceLimits
import RiemannResearch.RH.CanonicalCarryClosure
import RiemannResearch.RH.PhysicalPrimePowerCarryProjection
import RiemannResearch.NumberTheory.PrimePowerCRTDecomposition

/-! # Finite and limiting Gram energies for canonical mixed carries -/

noncomputable section

namespace RiemannResearch.RH.CanonicalCarryClosure

open Filter RiemannResearch.NumberTheory.PrimePowerCRT
open scoped Topology
open RiemannResearch.Analysis.HilbertConstraintReconstruction
open RiemannResearch.Analysis.FiniteHilbertGram
open PhysicalPrimePowerCarryProjection Pareto Pareto.CoefficientStabilization
open scoped ENNReal BigOperators

/-- Actual mixed raw-carry observations used in the Pareto Gram problem. -/
abbrev rawPVector (d : MixedConductor) : ThresholdHilbert :=
  canonicalVector pAtom d.val

def rawUnitObservation (d : MixedConductor) : ℝ :=
  inner ℝ (rawPVector d) hilbertOne

/-- The signed unit datum is an explicit logarithmic CRT row. -/
theorem rawUnitObservation_eq_log_row (d : MixedConductor) :
    rawUnitObservation d =
      (∑ p ∈ d.val.primeFactors, (NumberTheory.PrimePowerCRT.coefficient d.val p : ℝ) *
        (Real.log (modulus d.val p : ℝ) / (modulus d.val p : ℝ))) -
      Real.log (d.val : ℝ) / (d.val : ℝ) := by
  have hm (a : ℕ) (ha : 0 < a) : inner ℝ (pAtom a) hilbertOne = Real.log a / (a : ℝ) := by
    rw [pAtom, dif_pos ha]
    exact normalizedResidueHilbert_inner_one a ha
  rw [rawUnitObservation, rawPVector, canonicalVector, inner_sub_left, sum_inner,
    hm _ (lt_trans Nat.zero_lt_one d.property.1)]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rw [real_inner_smul_left, hm _ (modulus_pos _ _)]

/-- The quadratic Moore–Penrose cost of these prescribed signed observations. -/
def rawUnitGramCost (F : Finset MixedConductor) : ℝ :=
  ∑ i : F, rawUnitObservation i.val *
    gramPseudoinverse (fun j : F => rawPVector j.val) (fun j : F => rawUnitObservation j.val) i

/-- The actual constant witnesses finite feasibility even for a redundant dictionary. -/
theorem rawUnitGramCost_eq_finiteOptimum (F : Finset MixedConductor) :
    ENNReal.ofReal (rawUnitGramCost F) = finiteOptimum rawPVector rawUnitObservation F := by
  have hf : ∃ c : F → ℝ,
      gram (fun j : F => rawPVector j.val) c = (fun j : F => rawUnitObservation j.val) :=
    (finite_feasible_iff_gram_range _ _).mp ⟨hilbertOne, fun _ => rfl⟩
  exact (finiteConstraintEnergy_feasible _ _ hf).symm

/-- The exact cost captured by the whole raw-carry Gram dictionary. -/
theorem rawUnitGramCost_iSup :
    (⨆ F : Finset MixedConductor, ENNReal.ofReal (rawUnitGramCost F)) =
      ENNReal.ofReal (1 - limitEnergy) := by
  have hx : IsSolution rawPVector rawUnitObservation hilbertOne := fun _ => rfl
  have hspan : closedSpan rawPVector = closedSpace := physical_rawCarry_closures.1
  calc
    _ = ⨆ F : Finset MixedConductor, finiteOptimum rawPVector rawUnitObservation F := by
      simp_rw [rawUnitGramCost_eq_finiteOptimum]
    _ = ENNReal.ofReal (‖(closedSpan rawPVector).starProjection hilbertOne‖ ^ 2) :=
      (canonical_energy_eq_iSup rawPVector rawUnitObservation hx).symm
    _ = ENNReal.ofReal (1 - limitEnergy) := by
      simpa only [hspan, limitProjection] using
        congrArg ENNReal.ofReal limitProjection_norm_sq

/-- RH is saturation of the raw mixed-carry Gram costs for the unit moments. -/
theorem riemannHypothesis_iff_rawUnitGramCost_saturates :
    RiemannHypothesis ↔
      (⨆ F : Finset MixedConductor, ENNReal.ofReal (rawUnitGramCost F)) = 1 := by
  have hrh : RiemannHypothesis ↔ limitEnergy = 0 :=
    riemannHypothesis_iff_one_mem_canonicalCarryClosure.trans
      (by rw [physical_rawCarry_closures.1]; exact limitEnergy_zero_iff_mem.symm)
  rw [hrh, rawUnitGramCost_iSup]
  constructor
  · intro h
    simp [h]
  · intro h
    have hp : 0 ≤ 1 - limitEnergy := limitProjection_norm_sq ▸ sq_nonneg _
    have hh := congrArg ENNReal.toReal h
    rw [ENNReal.toReal_ofReal hp, ENNReal.toReal_one] at hh
    linarith

/-- Strong reconstruction from raw mixed carries alone returns the legal
projection of the actual constant. -/
theorem rawUnitGram_minimizers_tendsto :
    Tendsto (finiteMinimum rawPVector rawUnitObservation) atTop (𝓝 limitProjection) := by
  have hx : IsSolution rawPVector rawUnitObservation hilbertOne := fun _ => rfl
  have hspan : closedSpan rawPVector = closedSpace := physical_rawCarry_closures.1
  simpa only [hspan, limitProjection] using finiteMinimum_tendsto rawPVector rawUnitObservation hx

end RiemannResearch.RH.CanonicalCarryClosure

/-- info: 'RiemannResearch.RH.CanonicalCarryClosure.riemannHypothesis_iff_rawUnitGramCost_saturates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  RiemannResearch.RH.CanonicalCarryClosure.riemannHypothesis_iff_rawUnitGramCost_saturates

/-- info: 'RiemannResearch.RH.CanonicalCarryClosure.rawUnitGram_minimizers_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  RiemannResearch.RH.CanonicalCarryClosure.rawUnitGram_minimizers_tendsto
