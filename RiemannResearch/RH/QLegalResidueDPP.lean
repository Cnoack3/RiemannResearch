/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QDivisorProjectionDPP
import RiemannResearch.RH.QDivisorProjectionParity
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.QCovarianceInverse
import RiemannResearch.RH.QCovarianceInvertibility
import RiemannResearch.RH.QSquarefreeCapacity
import RiemannResearch.RH.QOptimizerParity
import RiemannResearch.RH.QOptimizerParityRH
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import RiemannResearch.Analysis.FiniteHilbertGramProjection
import RiemannResearch.Analysis.AtomSpanReweighting
import RiemannResearch.Probability.DeterminantalProcess
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# DPPs of the actual full and squarefree legal-residue projections

Source: user-provided legal-residue DPP/CRT proposal, 14 October 2026.
The Hilbert space, legal stages, inverse Gram and centered-capacity identities,
CRT closure equivalence and Mellin-to-RH consumers are all reused.
Site 1 is the constant divisor-wavelet mode, not a moving physical integer.

Each law is constructed unconditionally. Its constant vacancy is the full
optimizer error. Occupation tending to one, or the single parity kernel
entry tending to zero, is an explicit sufficient hypothesis for Mathlib RH.
The squarefree CRT version requires a uniformly bounded weighted tail.
No theorem in this module proves that arithmetic bound or either zero limit.
Nonzero column reweighting leaves the actual legal projection law unchanged.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QLegalResidueDPP
open ZetaTwoHilbert QDivisorProjectionDPP
open RiemannResearch.Analysis.ExhaustiveWalk
open QCovarianceInverse QCovarianceInvertibility
open RiemannResearch.Probability.DPP

def fullLaw (n : ℕ) : Measure (ℕ+ → Bool) := modeLaw (QFullResidueProjection.stage n)
def squarefreeLaw (n : ℕ) : Measure (ℕ+ → Bool) := modeLaw (ZetaTwoOptimizerStage.stage n)
instance fullLaw_probability (n : ℕ) : IsProbabilityMeasure (fullLaw n) := by
  unfold fullLaw
  infer_instance
instance squarefreeLaw_probability (n : ℕ) :
    IsProbabilityMeasure (squarefreeLaw n) := by
  unfold squarefreeLaw
  infer_instance

theorem fullLaw_isDPP (n : ℕ) :
    IsDPP (fullLaw n) (fun x => {r | x r = true})
      (modeKernel (QFullResidueProjection.stage n)) := modeLaw_isDPP _
theorem squarefreeLaw_isDPP (n : ℕ) :
    IsDPP (squarefreeLaw n) (fun x => {r | x r = true})
      (modeKernel (ZetaTwoOptimizerStage.stage n)) := modeLaw_isDPP _

def fullOccupation (n : ℕ) : ℝ := (fullLaw n).real {x | x 1 = true}
def squarefreeOccupation (n : ℕ) : ℝ := (squarefreeLaw n).real {x | x 1 = true}

theorem full_occupation_energy (n : ℕ) :
    fullOccupation n = 1 - ‖qOne - QFullResidueProjection.candidate n‖ ^ 2 := by
  have h := modeKernel_vacancy_energy (QFullResidueProjection.stage n) 1
  rw [normalized_one, ← QFullResidueProjection.candidate_eq_projection] at h
  rw [fullOccupation, fullLaw, modeLaw_occupation]
  linarith

theorem full_vacancy_energy (n : ℕ) :
    (fullLaw n).real {x | x 1 = false} =
      ‖qOne - QFullResidueProjection.candidate n‖ ^ 2 := by
  simpa only [fullLaw, ← QFullResidueProjection.candidate_eq_projection] using
    constant_vacancy (QFullResidueProjection.stage n)

theorem squarefree_occupation_energy (n : ℕ) :
    squarefreeOccupation n = 1 - ZetaTwoOptimizerStage.error n := by
  have h := modeKernel_vacancy_energy (ZetaTwoOptimizerStage.stage n) 1
  rw [normalized_one] at h
  rw [squarefreeOccupation, squarefreeLaw, modeLaw_occupation]
  change _ = 1 - ‖qOne - (ZetaTwoOptimizerStage.stage n).starProjection qOne‖ ^ 2
  linarith

theorem squarefree_vacancy_energy (n : ℕ) :
    (squarefreeLaw n).real {x | x 1 = false} = ZetaTwoOptimizerStage.error n := by
  exact constant_vacancy (ZetaTwoOptimizerStage.stage n)

theorem full_occupation_information (n : ℕ) :
    fullOccupation n = covarianceInformation (QFullResidueProjection.conductor n) /
      (1 + covarianceInformation (QFullResidueProjection.conductor n)) := by
  let d := QFullResidueProjection.conductor n
  have hd := QFullResidueProjection.conductor_gt_one n
  have hi := QFullResidueProjection.conductor_injective n
  have he := qError_genuine_inverse d hd hi
  have hc := gramInverseSource_eq_normalized_covariance d hd hi
  have hn := qInformation_nonneg d (covarianceInverseSource d)
    (covarianceInverseSource_normal d hd hi)
  change 0 ≤ covarianceInformation d at hn
  have hden : 1 + covarianceInformation d ≠ 0 := by linarith
  rw [full_occupation_energy, QFullResidueProjection.candidate,
    QFullResidueProjection.coefficients, hc, he]
  change 1 - 1 / (1 + covarianceInformation d) =
    covarianceInformation d / (1 + covarianceInformation d)
  field_simp [hden]
  ring

theorem squarefree_occupation_capacity (n : ℕ) :
    squarefreeOccupation n = QSquarefreeCapacity.capacity n /
      (1 + QSquarefreeCapacity.capacity n) := by
  have hn := QSquarefreeCapacity.capacity_nonneg n
  have hden : 1 + QSquarefreeCapacity.capacity n ≠ 0 := by linarith
  rw [squarefree_occupation_energy, QSquarefreeCapacity.error_eq_reciprocal_capacity]
  field_simp
  ring

theorem fullOccupation_monotone : Monotone fullOccupation := by
  intro n m hnm
  simpa only [fullOccupation, fullLaw, modeLaw_occupation] using
    modeKernel_diagonal_mono (QFullResidueProjection.stage n)
      (QFullResidueProjection.stage m)
      (walkSpan_mono (fun i => qResidue (i + 2)) id hnm) 1

theorem squarefreeOccupation_monotone : Monotone squarefreeOccupation := by
  intro n m hnm
  simpa only [squarefreeOccupation, squarefreeLaw, modeLaw_occupation] using
    modeKernel_diagonal_mono (ZetaTwoOptimizerStage.stage n)
      (ZetaTwoOptimizerStage.stage m)
      (walkSpan_mono ZetaTwoOptimizerStage.squarefreeAtom id hnm) 1

theorem fullOccupation_tendsto_projection :
    Tendsto fullOccupation atTop
      (𝓝 (‖QFullResidueProjection.closure.starProjection qOne‖ ^ 2)) := by
  have h := QFullResidueProjection.candidate_tendsto_projection.norm.pow 2
  change Tendsto (fun n => fullOccupation n) atTop _
  simpa only [fullOccupation, fullLaw, constant_occupation,
    ← QFullResidueProjection.candidate_eq_projection] using h

theorem fullOccupation_tendsto_one_iff :
    Tendsto fullOccupation atTop (𝓝 1) ↔ qOne ∈ QFullResidueProjection.closure := by
  rw [← QFullResidueProjection.residual_energy_tendsto_zero_iff]
  constructor
  · intro h
    have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    simpa only [full_occupation_energy, sub_sub_cancel, sub_self] using hc.sub h
  · intro h
    have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    simpa only [← full_occupation_energy, sub_zero] using hc.sub h

theorem squarefreeOccupation_tendsto_one_iff :
    Tendsto squarefreeOccupation atTop (𝓝 1) ↔ qOne ∈ ZetaTwoOptimizerStage.closure := by
  rw [← ZetaTwoOptimizerStage.error_tendsto_zero_iff_mem_closure]
  constructor
  · intro h
    have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    simpa only [squarefree_occupation_energy, sub_sub_cancel, sub_self] using hc.sub h
  · intro h
    have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    simpa only [← squarefree_occupation_energy, sub_zero] using hc.sub h

theorem squarefreeOccupation_tendsto_one_iff_capacity :
    Tendsto squarefreeOccupation atTop (𝓝 1) ↔
      Tendsto QSquarefreeCapacity.capacity atTop atTop :=
  squarefreeOccupation_tendsto_one_iff.trans
    QSquarefreeCapacity.capacity_tendsto_iff_optimizer_closure.symm

theorem squarefreeOccupation_tendsto_one_iff_CRT :
    Tendsto squarefreeOccupation atTop (𝓝 1) ↔ Pareto.SquarefreeExactHeadTailBound :=
  squarefreeOccupation_tendsto_one_iff_capacity.trans
    QSquarefreeCapacity.capacity_tendsto_iff_exact_head_tail_bound

theorem riemannHypothesis_of_fullOccupation_tendsto_one
    (h : Tendsto fullOccupation atTop (𝓝 1)) : RiemannHypothesis :=
  QFullResidueProjection.riemannHypothesis_of_qOne_mem_full_closure
    (fullOccupation_tendsto_one_iff.mp h)

theorem riemannHypothesis_of_squarefreeOccupation_tendsto_one
    (h : Tendsto squarefreeOccupation atTop (𝓝 1)) : RiemannHypothesis :=
  QSquarefreeCapacity.riemannHypothesis_of_capacity_tendsto
    (squarefreeOccupation_tendsto_one_iff_capacity.mp h)

theorem full_parity_kernel (n : ℕ) (hn : 0 < n) :
    modeKernel (QFullResidueProjection.stage n) 1 2 =
      -Real.sqrt 3 * (1 - fullOccupation n) := by
  simpa only [fullOccupation, fullLaw, modeLaw_occupation] using
    constant_parity_kernel (QFullResidueProjection.stage n)
      (QFullResidueProjection.qResidue_two_mem_stage n hn)

end RiemannResearch.RH.QLegalResidueDPP

namespace RiemannResearch.RH.QLegalResidueDPP
open ZetaTwoHilbert QDivisorProjectionDPP
open RiemannResearch.Analysis.ExhaustiveWalk

theorem fullOccupation_lt_one (n : ℕ) : fullOccupation n < 1 := by
  rw [full_occupation_energy]
  have h := QFullResidueProjection.residual_energy_pos n
  linarith

theorem squarefreeOccupation_lt_one (n : ℕ) : squarefreeOccupation n < 1 := by
  rw [squarefree_occupation_energy]
  have h := ZetaTwoOptimizerStage.error_pos n
  linarith

theorem qResidue_two_mem_squarefree_stage (n : ℕ) (hn : 0 < n) :
    qResidue 2 ∈ ZetaTwoOptimizerStage.stage n := by
  change qResidue 2 ∈ Submodule.span ℝ
    (Set.range (fun i : Fin n => ZetaTwoOptimizerStage.squarefreeAtom (id (i : ℕ))))
  have h : ZetaTwoOptimizerStage.squarefreeAtom 0 ∈
      Submodule.span ℝ
        (Set.range (fun i : Fin n => ZetaTwoOptimizerStage.squarefreeAtom (id (i : ℕ)))) :=
    Submodule.subset_span ⟨⟨0, hn⟩, rfl⟩
  simpa [ZetaTwoOptimizerStage.squarefreeAtom, Nat.prime_two.squarefree] using h

theorem squarefree_parity_kernel (n : ℕ) (hn : 0 < n) :
    modeKernel (ZetaTwoOptimizerStage.stage n) 1 2 =
      -Real.sqrt 3 * (1 - squarefreeOccupation n) := by
  simpa only [squarefreeOccupation, squarefreeLaw, modeLaw_occupation] using
    constant_parity_kernel (ZetaTwoOptimizerStage.stage n)
      (qResidue_two_mem_squarefree_stage n hn)

theorem full_parity_kernel_tendsto_zero_iff :
    Tendsto (fun n => modeKernel (QFullResidueProjection.stage n) 1 2)
      atTop (𝓝 0) ↔ Tendsto fullOccupation atTop (𝓝 1) := by
  have heq : (fun n => modeKernel (QFullResidueProjection.stage n) 1 2) =ᶠ[atTop]
      (fun n => -Real.sqrt 3 * (1 - fullOccupation n)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact full_parity_kernel n (by omega)
  rw [tendsto_congr' heq]
  have hn : -Real.sqrt (3 : ℝ) ≠ 0 := neg_ne_zero.mpr
    (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))
  constructor
  · intro h
    have hv := h.const_mul (-Real.sqrt (3 : ℝ))⁻¹
    have he : Tendsto (fun n => 1 - fullOccupation n) atTop (𝓝 0) := by
      simpa only [← mul_assoc, inv_mul_cancel₀ hn, one_mul, mul_zero] using hv
    have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    simpa only [sub_sub_cancel, sub_zero] using hc.sub he
  · intro h
    have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    simpa only [sub_self, mul_zero] using (hc.sub h).const_mul (-Real.sqrt 3)

theorem squarefree_parity_kernel_tendsto_zero_iff :
    Tendsto (fun n => modeKernel (ZetaTwoOptimizerStage.stage n) 1 2)
      atTop (𝓝 0) ↔ Tendsto squarefreeOccupation atTop (𝓝 1) := by
  have heq : (fun n => modeKernel (ZetaTwoOptimizerStage.stage n) 1 2) =ᶠ[atTop]
      (fun n => -Real.sqrt 3 * (1 - squarefreeOccupation n)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact squarefree_parity_kernel n (by omega)
  rw [tendsto_congr' heq]
  have hn : -Real.sqrt (3 : ℝ) ≠ 0 := neg_ne_zero.mpr
    (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))
  constructor
  · intro h
    have hv := h.const_mul (-Real.sqrt (3 : ℝ))⁻¹
    have he : Tendsto (fun n => 1 - squarefreeOccupation n) atTop (𝓝 0) := by
      simpa only [← mul_assoc, inv_mul_cancel₀ hn, one_mul, mul_zero] using hv
    have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    simpa only [sub_sub_cancel, sub_zero] using hc.sub he
  · intro h
    have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    simpa only [sub_self, mul_zero] using (hc.sub h).const_mul (-Real.sqrt 3)

theorem riemannHypothesis_of_full_parity_kernel_tendsto_zero
    (h : Tendsto (fun n => modeKernel (QFullResidueProjection.stage n) 1 2)
      atTop (𝓝 0)) : RiemannHypothesis :=
  riemannHypothesis_of_fullOccupation_tendsto_one (full_parity_kernel_tendsto_zero_iff.mp h)

theorem riemannHypothesis_of_squarefree_parity_kernel_tendsto_zero
    (h : Tendsto (fun n => modeKernel (ZetaTwoOptimizerStage.stage n) 1 2)
      atTop (𝓝 0)) : RiemannHypothesis :=
  riemannHypothesis_of_squarefreeOccupation_tendsto_one
    (squarefree_parity_kernel_tendsto_zero_iff.mp h)
end RiemannResearch.RH.QLegalResidueDPP

namespace RiemannResearch.RH.QLegalResidueDPP
open ZetaTwoHilbert QDivisorProjectionDPP
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.AtomSpanReweighting

/-- A genuine full-Q trial-energy estimate suffices; pointwise estimates alone do not. -/
theorem fullOccupation_tendsto_one_of_trial_error
    (F : ℕ → QHilbert) (hF : ∀ n, F n ∈ QFullResidueProjection.stage n)
    (herror : Tendsto (fun n => ‖qOne - F n‖ ^ 2) atTop (𝓝 0)) :
    Tendsto fullOccupation atTop (𝓝 1) := by
  have hv : Tendsto (fun n => (fullLaw n).real {x | x 1 = false})
      atTop (𝓝 0) :=
    squeeze_zero (fun _ => measureReal_nonneg)
      (fun n => constant_vacancy_le_trial_error (QFullResidueProjection.stage n)
        (F n) (hF n)) herror
  apply fullOccupation_tendsto_one_iff.mpr
  apply QFullResidueProjection.residual_energy_tendsto_zero_iff.mp
  simpa only [full_vacancy_energy] using hv

/-- Nonzero column weights do not change the legal subspace. -/
def reweightedStage (n : ℕ) (a : Fin n → ℝ) : Submodule ℝ QHilbert :=
  synthesisSpan (fun i => a i • qResidue (QFullResidueProjection.conductor n i))

instance reweightedStage_finiteDimensional (n : ℕ) (a : Fin n → ℝ) :
    FiniteDimensional ℝ (reweightedStage n a) := by
  unfold reweightedStage
  infer_instance

theorem reweightedStage_eq (n : ℕ) (a : Fin n → ℝ) (ha : ∀ i, a i ≠ 0) :
    reweightedStage n a = QFullResidueProjection.stage n := by
  simpa only [reweightedStage, synthesisSpan, QFullResidueProjection.stage,
    RiemannResearch.Analysis.ExhaustiveWalk.walkSpan,
    QFullResidueProjection.conductor, id_eq] using
      span_range_smul_eq (fun i : Fin n => qResidue (QFullResidueProjection.conductor n i))
        a ha

theorem reweighted_modeLaw_eq (n : ℕ) (a : Fin n → ℝ) (ha : ∀ i, a i ≠ 0) :
    modeLaw (reweightedStage n a) = fullLaw n := by
  simp only [reweightedStage_eq n a ha, fullLaw]

end RiemannResearch.RH.QLegalResidueDPP
