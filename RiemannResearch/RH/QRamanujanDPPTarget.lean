import RiemannResearch.RH.QRamanujanDPPHoleEnergy
import RiemannResearch.Probability.DeterminantalExistence

/-!
# Joint Q observation laws containing the normalized constant target

Source: sixth transfer program, 24 October 2026. A finite orthonormal family
of actual Q vectors defines a joint projection DPP. The target is explicitly
required to occur in this family. Other observations are not assumed to lie
in the legal closure. The RH converse retains the open Baez--Duarte provider.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical Topology
namespace RiemannResearch.RH.QRamanujanDPP
open Pareto ZetaTwoHilbert QRamanujanCanonicalOptimizer
open RiemannResearch.Probability.DPP
open RiemannResearch.Analysis.ProjectionDPP

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def probeKernel (e : ι → QHilbert) (n : ℕ) : Matrix ι ι ℝ :=
  Matrix.of (RiemannResearch.Analysis.ProjectionDPP.kernel (QFullResidueProjection.stage n) e)

def limitProbeKernel (e : ι → QHilbert) : Matrix ι ι ℝ :=
  Matrix.of (RiemannResearch.Analysis.ProjectionDPP.kernel QFullResidueProjection.closure e)

theorem probe_exactWeight_nonneg (e : ι → QHilbert)
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0) (n : ℕ) (S : Finset ι) :
    0 ≤ exactWeight (probeKernel e n) S :=
  exactWeight_nonneg _ (principal_posSemidef (QFullResidueProjection.stage n) e id)
    (identity_sub_principal_posSemidef (QFullResidueProjection.stage n) e id he) S

theorem limitProbe_exactWeight_nonneg (e : ι → QHilbert)
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0) (S : Finset ι) :
    0 ≤ exactWeight (limitProbeKernel e) S :=
  exactWeight_nonneg _ (principal_posSemidef QFullResidueProjection.closure e id)
    (identity_sub_principal_posSemidef QFullResidueProjection.closure e id he) S

def probeLaw (e : ι → QHilbert)
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0) (n : ℕ) : Measure (ι → Bool) :=
  (finiteBoolLaw (probeKernel e n) (probe_exactWeight_nonneg e he n)).toMeasure

def limitProbeLaw (e : ι → QHilbert)
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0) : Measure (ι → Bool) :=
  (finiteBoolLaw (limitProbeKernel e) (limitProbe_exactWeight_nonneg e he)).toMeasure

instance probeLaw_probability (e : ι → QHilbert)
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0) (n : ℕ) :
    IsProbabilityMeasure (probeLaw e he n) := by unfold probeLaw; infer_instance

instance limitProbeLaw_probability (e : ι → QHilbert)
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0) :
    IsProbabilityMeasure (limitProbeLaw e he) := by unfold limitProbeLaw; infer_instance

theorem probeLaw_isDPP (e : ι → QHilbert)
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0) (n : ℕ) :
    IsDPP (probeLaw e he n) (fun x => {i | x i = true}) (probeKernel e n) :=
  finiteBoolLaw_isDPP _ _

theorem limitProbeLaw_isDPP (e : ι → QHilbert)
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0) :
    IsDPP (limitProbeLaw e he) (fun x => {i | x i = true}) (limitProbeKernel e) :=
  finiteBoolLaw_isDPP _ _

theorem probe_target_diagonal (e : ι → QHilbert) (t : ι) (ht : e t = qOne) (n : ℕ) :
    probeKernel e n t t = packetMass n := by
  have hh := RiemannResearch.Analysis.ProjectionDPP.holeKernel_eq
    (QFullResidueProjection.stage n) e t t
  rw [RiemannResearch.Analysis.ProjectionDPP.holeKernel_diagonal, ht,
    real_inner_self_eq_norm_sq, qOne_norm_sq] at hh
  have herr : ‖qOne - (QFullResidueProjection.stage n).starProjection qOne‖ ^ 2 =
      1 - packetMass n := by
    rw [← QFullResidueProjection.candidate_eq_projection,
      ← packetCandidate_eq_residueCandidate]
    exact packet_error n
  change ‖qOne - (QFullResidueProjection.stage n).starProjection qOne‖ ^ 2 =
    1 - probeKernel e n t t at hh
  linarith

theorem limitProbe_target_diagonal (e : ι → QHilbert) (t : ι) (ht : e t = qOne) :
    limitProbeKernel e t t = 1 - packetLimitEnergy := by
  have hh := RiemannResearch.Analysis.ProjectionDPP.holeKernel_eq
    QFullResidueProjection.closure e t t
  rw [RiemannResearch.Analysis.ProjectionDPP.holeKernel_diagonal, ht,
    real_inner_self_eq_norm_sq, qOne_norm_sq] at hh
  change packetLimitEnergy = 1 - limitProbeKernel e t t at hh
  linarith

theorem probe_target_vacancy (e : ι → QHilbert)
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0)
    (t : ι) (ht : e t = qOne) (n : ℕ) :
    (probeLaw e he n).real {x | x t = false} = packetError n := by
  have h := (probeLaw_isDPP e he n).vacancy t
  rw [probe_target_diagonal e t ht n] at h
  simpa [packetError] using h

theorem limitProbe_target_vacancy (e : ι → QHilbert)
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0)
    (t : ι) (ht : e t = qOne) :
    (limitProbeLaw e he).real {x | x t = false} = packetLimitEnergy := by
  have h := (limitProbeLaw_isDPP e he).vacancy t
  rw [limitProbe_target_diagonal e t ht] at h
  simpa using h

/-- Full occupation needs membership for every chosen test vector, explicitly. -/
theorem limitProbe_full_occupation_iff (e : ι → QHilbert)
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0) :
    (∀ᵐ x ∂limitProbeLaw e he, {i | x i = true} = Set.univ) ↔
      ∀ i, e i ∈ QFullResidueProjection.closure := by
  rw [(limitProbeLaw_isDPP e he).full_occupation_ae_iff]
  apply forall_congr'
  intro i
  have hi : ‖e i‖ ^ 2 = 1 := by
    simpa only [real_inner_self_eq_norm_sq, if_true] using he i i
  simpa only [limitProbeKernel, Matrix.of_apply] using
    (diagonal_one_iff QFullResidueProjection.closure e i hi)

theorem packetLimitEnergy_zero_iff_rh
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation) :
    packetLimitEnergy = 0 ↔ RiemannHypothesis :=
  packetLimitEnergy_zero_iff_closure.trans
    (packetCoordinate_limits_moebius_iff_closure.symm.trans
      (packetCoordinate_limits_iff_rh hBaezDuarte))

/-- Joint target-observation, canonical coefficients, and full complementary energy criteria. -/
theorem target_joint_rh_equivalences
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation)
    (e : ι → QHilbert)
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0)
    (t : ι) (ht : e t = qOne) :
    (Tendsto (fun n => (probeLaw e he n).real {x | x t = false}) atTop (𝓝 0) ↔
      RiemannHypothesis) ∧
    ((∀ᵐ x ∂limitProbeLaw e he, x t = true) ↔ RiemannHypothesis) ∧
    (Tendsto (fun M => ∑ i : Fin M, ∑ j : Fin M, qOne i * qOne j * limitHoleKernel i j)
      atTop (𝓝 0) ↔ RiemannHypothesis) := by
  have hz := packetLimitEnergy_zero_iff_rh hBaezDuarte
  have hv : Tendsto packetError atTop (𝓝 0) ↔ packetLimitEnergy = 0 := by
    constructor
    · exact fun h => tendsto_nhds_unique packetError_tendsto h
    · intro h
      simpa only [h] using packetError_tendsto
  refine ⟨?_, ?_, ?_⟩
  · simpa only [probe_target_vacancy e he t ht] using hv.trans hz
  · have ho := (limitProbeLaw_isDPP e he).mem_ae_iff t
    simp only [Set.mem_ofPred_eq] at ho
    rw [ho, limitProbe_target_diagonal e t ht]
    exact (by constructor <;> intro h <;> linarith :
      1 - packetLimitEnergy = 1 ↔ packetLimitEnergy = 0).trans hz
  · exact target_hole_energy_zero_iff_closure.trans
      (packetLimitEnergy_zero_iff_closure.symm.trans hz)

end RiemannResearch.RH.QRamanujanDPP
