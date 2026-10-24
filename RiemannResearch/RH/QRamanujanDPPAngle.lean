import RiemannResearch.Analysis.ProjectionConditioningBound
import RiemannResearch.RH.QRamanujanDPPConditioning

/-!
# A dimension-independent conditioning bound for actual Q projections

Source: elementary projection geometry applied to the user's Transfer 100
conditioning problem, 24 October 2026.

The source of the bound is a quantitative angle between the auxiliary span
and the current legal projection kernel. This hypothesis controls the entire
span, not merely the individual probes. The RH application still requires
the explicit open Baez--Duarte provider.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical Topology

namespace RiemannResearch.RH.QRamanujanDPP
open Pareto ZetaTwoHilbert QRamanujanCanonicalOptimizer
open RiemannResearch.Analysis.FiniteHilbertGram

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem target_orthogonal_headSpan (e : Option ι → QHilbert)
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0)
    (ht : e none = qOne) :
    ∀ v ∈ synthesisSpan (fun i => e (some i)), inner ℝ qOne v = 0 := by
  intro v hv
  rw [synthesisSpan, ← Fintype.range_linearCombination] at hv
  obtain ⟨c, rfl⟩ := hv
  simp only [Fintype.linearCombination_apply, inner_sum, inner_smul_right]
  apply Finset.sum_eq_zero
  intro i _
  have hz : inner ℝ qOne (e (some i)) = 0 := by
    rw [← ht, he]
    simp
  rw [hz, mul_zero]

theorem packetError_eq_projection_error (n : ℕ) :
    packetError n = ‖qOne - (QFullResidueProjection.stage n).starProjection qOne‖ ^ 2 := by
  rw [← QFullResidueProjection.candidate_eq_projection,
    ← packetCandidate_eq_residueCandidate]
  exact (packet_error n).symm

theorem projectedHead_independent_of_loss_bound
    (e : Option ι → QHilbert)
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0)
    (n : ℕ) (ρ : ℝ) (hρ1 : ρ < 1)
    (hloss : ∀ v ∈ synthesisSpan (fun i => e (some i)),
      ‖v - (QFullResidueProjection.stage n).starProjection v‖ ^ 2 ≤ ρ * ‖v‖ ^ 2) :
    LinearIndependent ℝ (projectedHead e n) := by
  have hon : Orthonormal ℝ (fun i => e (some i)) := by
    apply orthonormal_iff_ite.mpr
    intro i j
    simpa only [Option.some.injEq] using he (some i) (some j)
  exact projected_independent_of_loss_bound (QFullResidueProjection.stage n)
    (fun i => e (some i)) hon.linearIndependent ρ hρ1 hloss

theorem conditioningCost_mul_le_of_loss_bound
    (e : Option ι → QHilbert)
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0)
    (ht : e none = qOne) (n : ℕ) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hloss : ∀ v ∈ synthesisSpan (fun i => e (some i)),
      ‖v - (QFullResidueProjection.stage n).starProjection v‖ ^ 2 ≤ ρ * ‖v‖ ^ 2) :
    (1 - ρ) * conditioningCost e n ≤ ρ * packetError n := by
  have h := conditioning_projection_mul_bound (QFullResidueProjection.stage n)
    (fun i => e (some i)) qOne ρ hρ0 hρ1
    (target_orthogonal_headSpan e he ht) hloss
  dsimp only [conditioningCost, projectedHead]
  rw [packetError_eq_projection_error]
  exact h

/-- The bound is independent of the head cardinality and of the head-inclusion mass. -/
theorem conditionedVacancy_le_of_loss_bound
    (e : Option ι → QHilbert)
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0)
    (ht : e none = qOne) (n : ℕ) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hloss : ∀ v ∈ synthesisSpan (fun i => e (some i)),
      ‖v - (QFullResidueProjection.stage n).starProjection v‖ ^ 2 ≤ ρ * ‖v‖ ^ 2) :
    conditionedVacancy e he n ≤ packetError n / (1 - ρ) := by
  have hi := projectedHead_independent_of_loss_bound e he n ρ hρ1 hloss
  rw [conditionedVacancy_eq e he ht n hi]
  apply (le_div_iff₀ (sub_pos.mpr hρ1)).mpr
  have h := conditioningCost_mul_le_of_loss_bound e he ht n ρ hρ0 hρ1 hloss
  nlinarith

/-- A uniform angle bound suffices even for genuinely growing finite heads.
No uniform positive lower bound on their full inclusion probabilities is assumed.
The RH converse still uses the explicitly supplied Baez--Duarte provider. -/
theorem growing_conditioned_vacancy_iff_rh_of_span_loss
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation)
    {α : Type*} {l : Filter α} [NeBot l]
    (κ : α → Type*) [∀ a, Fintype (κ a)] [∀ a, DecidableEq (κ a)]
    (N : α → ℕ) (hN : Tendsto N l atTop)
    (e : (a : α) → Option (κ a) → QHilbert)
    (he : ∀ a i j, inner ℝ (e a i) (e a j) = if i = j then 1 else 0)
    (ht : ∀ a, e a none = qOne)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hloss : ∀ᶠ a in l, ∀ v ∈ synthesisSpan (fun i => e a (some i)),
      ‖v - (QFullResidueProjection.stage (N a)).starProjection v‖ ^ 2 ≤ ρ * ‖v‖ ^ 2) :
    Tendsto (fun a => conditionedVacancy (e a) (he a) (N a)) l (𝓝 0) ↔
      RiemannHypothesis := by
  have hlim : Tendsto (fun a => packetError (N a)) l (𝓝 packetLimitEnergy) := by
    simpa only [Function.comp_def] using packetError_tendsto.comp hN
  have hb : ∀ᶠ a in l,
      packetError (N a) ≤ conditionedVacancy (e a) (he a) (N a) ∧
      conditionedVacancy (e a) (he a) (N a) ≤ packetError (N a) / (1 - ρ) := by
    filter_upwards [hloss] with a ha
    have hi := projectedHead_independent_of_loss_bound (e a) (he a) (N a) ρ hρ1 ha
    exact ⟨(conditionedVacancy_bounds (e a) (he a) (ht a) (N a) hi).1,
      conditionedVacancy_le_of_loss_bound (e a) (he a) (ht a) (N a) ρ hρ0 hρ1 ha⟩
  constructor
  · intro hc
    have hz : Tendsto (fun a => packetError (N a)) l (𝓝 0) :=
      squeeze_zero' (Filter.Eventually.of_forall (fun a => (packetError_pos (N a)).le))
        (hb.mono (fun _ ha => ha.1)) hc
    exact (packetLimitEnergy_zero_iff_rh hBaezDuarte).mp (tendsto_nhds_unique hlim hz)
  · intro hrh
    have hz : Tendsto (fun a => packetError (N a)) l (𝓝 0) := by
      simpa only [(packetLimitEnergy_zero_iff_rh hBaezDuarte).mpr hrh] using hlim
    apply squeeze_zero'
      (hb.mono (fun a ha => (packetError_pos (N a)).le.trans ha.1))
      (hb.mono (fun _ ha => ha.2))
    simpa only [zero_div] using hz.div_const (1 - ρ)


theorem conditionedVacancy_eq_packetError_of_mem_stage
    (e : Option ι → QHilbert)
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0)
    (ht : e none = qOne) (n : ℕ)
    (hm : ∀ i, e (some i) ∈ QFullResidueProjection.stage n) :
    conditionedVacancy e he n = packetError n := by
  have hs : synthesisSpan (fun i => e (some i)) ≤ QFullResidueProjection.stage n := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hm i
  have hloss : ∀ v ∈ synthesisSpan (fun i => e (some i)),
      ‖v - (QFullResidueProjection.stage n).starProjection v‖ ^ 2 ≤ (0 : ℝ) * ‖v‖ ^ 2 := by
    intro v hv
    rw [Submodule.starProjection_eq_self_iff.mpr (hs hv)]
    simp
  have hi := projectedHead_independent_of_loss_bound e he n 0 (by norm_num) hloss
  have hb := conditionedVacancy_bounds e he ht n hi
  have hu := conditionedVacancy_le_of_loss_bound e he ht n 0 (by norm_num) (by norm_num) hloss
  exact le_antisymm (by simpa using hu) hb.1

end RiemannResearch.RH.QRamanujanDPP
