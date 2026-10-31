/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QCovarianceInvertibility
import RiemannResearch.RH.QCovarianceInverse
import RiemannResearch.RH.QRamanujanPackets
import RiemannResearch.RH.QSquarefreeInverseCapacity
import RiemannResearch.RH.QLegalResidueDPP
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import RiemannResearch.Analysis.FiniteHilbertGramProjection
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Canonical complete-squarefree Ramanujan coefficients

Source: the user's 30 October 2026 coefficient-construction request.
The complete Q Gram solve is restricted to every squarefree conductor in
2,...,N+1, including composites. Its packet transform is exact on that same
finite dictionary. The unconditional limit is the existing squarefree
projection, not an asserted constant. No asymptotic arithmetic estimate is
assumed or established by these identities.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QSquarefreeRamanujanProjection
open ZetaTwoHilbert QCovarianceInverse QCovarianceInvertibility QRamanujanPackets
open QSquarefreeInverseCapacity
open RiemannResearch.Analysis.FiniteHilbertGram

private theorem residue_independent (N : ℕ) :
    LinearIndependent ℝ (fun i : Index N => qResidue (conductor N i)) :=
  qResidue_linearIndependent (conductor N) (conductor_gt_one N) (conductor_injective N)

private theorem coefficients_eq_inverseCoeff (N : ℕ) :
    coefficients N = inverseCoeff (residue_independent N) qOne := by
  apply (residue_independent N).fintypeLinearCombination_injective
  change candidate N = _
  rw [candidate_eq_optimizer]
  symm
  simpa only [synthesisSpan, residue_span_eq_stage, ZetaTwoOptimizerStage.optimizer] using
    synthesis_inverseCoeff_eq_projection (residue_independent N) qOne

/-- The existing inverse-covariance coefficients are the literal Gram inverse solve. -/
theorem coefficients_eq_inverseGram (N : ℕ) :
    coefficients N = (residueGramMatrix (conductor N))⁻¹.mulVec (qMean (conductor N)) := by
  have hm : qMean (conductor N) =
      cross (fun i => qResidue (conductor N i)) qOne := by
    funext i
    exact (real_inner_comm qOne (qResidue (conductor N i))).symm
  change coefficients N = (gramMatrix (fun i => qResidue (conductor N i)))⁻¹.mulVec _
  rw [hm, gramMatrix_inverseSource (residue_independent N)]
  exact coefficients_eq_inverseCoeff N

/-- Every squarefree conductor in the cutoff; no coefficient is required to be nonzero. -/
def conductors (N : ℕ) : Finset ℕ := (Finset.Icc 2 (N + 1)).filter Squarefree

theorem mem_conductors (N q : ℕ) :
    q ∈ conductors N ↔ 2 ≤ q ∧ q ≤ N + 1 ∧ Squarefree q := by
  simp only [conductors, Finset.mem_filter, Finset.mem_Icc]
  tauto

theorem conductor_mem (N : ℕ) (i : Index N) :
    conductor N i ∈ conductors N := by
  rw [mem_conductors]
  exact ⟨by unfold conductor; omega, by unfold conductor; omega, i.property⟩

theorem packetSupport_gt_one_mem (N q : ℕ)
    (hq : q ∈ packetSupport (conductor N)) (hq1 : 1 < q) : q ∈ conductors N := by
  obtain ⟨i, _, hqi⟩ := Finset.mem_biUnion.mp hq
  have hd := Nat.dvd_of_mem_divisors hqi
  have hle := Nat.le_of_dvd (by have := conductor_gt_one N i; omega) hd
  rw [mem_conductors]
  exact ⟨by omega, by have := (mem_conductors N (conductor N i)).mp (conductor_mem N i); omega,
    i.property.squarefree_of_dvd hd⟩

theorem conductors_subset_packetSupport (N : ℕ) :
    conductors N ⊆ packetSupport (conductor N) := by
  intro q hq
  obtain ⟨hq2, hqN, hsf⟩ := (mem_conductors N q).mp hq
  let i : Index N := ⟨⟨q - 2, by omega⟩, by simpa [show q - 2 + 2 = q by omega]⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨i, Finset.mem_univ _, ?_⟩
  have he : conductor N i = q := by dsimp [conductor, i]; omega
  rw [he]
  exact Nat.mem_divisors.mpr ⟨dvd_refl q, by omega⟩

/-- A_(N,q) = sum over squarefree d in the cutoff divisible by q of alpha_d/d. -/
def packetCoefficients (N q : ℕ) : ℝ :=
  packetCoefficient (conductor N) (coefficients N) q

theorem packetCoefficients_formula (N q : ℕ) :
    packetCoefficients N q = ∑ i : Index N,
      if q ∣ conductor N i then coefficients N i / (conductor N i : ℝ) else 0 := rfl

/-- Exact canonical representation over the complete squarefree cutoff itself. -/
theorem candidate_eq_packets (N : ℕ) :
    candidate N = ∑ q ∈ conductors N, packetCoefficients N q • qRamanujanPacket q := by
  classical
  rw [candidate, qSynthesis_eq_packets (conductor N) (coefficients N)
    (fun i => by have := conductor_gt_one N i; omega)]
  symm
  apply Finset.sum_subset (conductors_subset_packetSupport N)
  intro q hq hnot
  have hqpos : 0 < q := by
    obtain ⟨i, _, hqi⟩ := Finset.mem_biUnion.mp hq
    exact Nat.pos_of_mem_divisors hqi
  have hq1 : q = 1 := by
    by_contra hne
    exact hnot (packetSupport_gt_one_mem N q hq (by omega))
  simp [hq1]

/-- The entire infinite Q error is the constant-target inverse-Gram deficit. -/
theorem error_eq_inverseGram (N : ℕ) :
    ZetaTwoOptimizerStage.error N = 1 - dotProduct (qMean (conductor N))
      ((residueGramMatrix (conductor N))⁻¹.mulVec (qMean (conductor N))) := by
  have h := residual_schur_value (residue_independent N) qOne
  rw [← coefficients_eq_inverseCoeff N] at h
  change ‖qOne - candidate N‖ ^ 2 = _ at h
  rw [candidate_eq_optimizer, qOne_norm_sq] at h
  change ZetaTwoOptimizerStage.error N = _ at h
  rw [h, ← coefficients_eq_inverseGram]
  congr 1
  unfold dotProduct cross qMean
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm (qResidue (conductor N i)) qOne]
  ring

theorem packet_sum_tendsto_projection :
    Tendsto (fun N => ∑ q ∈ conductors N,
      packetCoefficients N q • qRamanujanPacket q) atTop
      (𝓝 (ZetaTwoOptimizerStage.closure.starProjection qOne)) := by
  simp_rw [← candidate_eq_packets, candidate_eq_optimizer]
  exact ZetaTwoOptimizerStage.optimizer_tendsto

/-- Conditional research reduction: the inverse-Gram saturation remains open. -/
theorem inverseGram_tendsto_one_iff_closure :
    Tendsto (fun N => dotProduct (qMean (conductor N))
      ((residueGramMatrix (conductor N))⁻¹.mulVec (qMean (conductor N))))
        atTop (𝓝 1) ↔ qOne ∈ ZetaTwoOptimizerStage.closure := by
  rw [← ZetaTwoOptimizerStage.error_tendsto_zero_iff_mem_closure]
  have he : ZetaTwoOptimizerStage.error =
      fun N => 1 - dotProduct (qMean (conductor N))
      ((residueGramMatrix (conductor N))⁻¹.mulVec (qMean (conductor N))) :=
    funext error_eq_inverseGram
  rw [he]
  constructor
  · intro h
    simpa using (tendsto_const_nhds.sub h :
      Tendsto (fun N => (1 : ℝ) - dotProduct (qMean (conductor N))
      ((residueGramMatrix (conductor N))⁻¹.mulVec (qMean (conductor N))))
        atTop (𝓝 (1 - 1)))
  · intro h
    have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have ht := hc.sub h
    simpa using (ht : Tendsto (fun N => (1 : ℝ) -
      (1 - dotProduct (qMean (conductor N))
      ((residueGramMatrix (conductor N))⁻¹.mulVec (qMean (conductor N))))) atTop (𝓝 (1 - 0)))

/-- The sole domain-specific hypothesis is the still-open target saturation. -/
theorem riemannHypothesis_of_inverseGram_tendsto_one
    (h : Tendsto (fun N => dotProduct (qMean (conductor N))
      ((residueGramMatrix (conductor N))⁻¹.mulVec (qMean (conductor N))))
      atTop (𝓝 1)) : RiemannHypothesis :=
  QLegalResidueDPP.riemannHypothesis_of_squarefreeOccupation_tendsto_one
    (QLegalResidueDPP.squarefreeOccupation_tendsto_one_iff.mpr
      (inverseGram_tendsto_one_iff_closure.mp h))

end RiemannResearch.RH.QSquarefreeRamanujanProjection
