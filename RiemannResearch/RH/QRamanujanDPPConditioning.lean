import RiemannResearch.RH.QRamanujanDPPTarget
import RiemannResearch.Probability.DeterminantalConditioning
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# Exact target conditioning and a moving-event RH criterion in Q

Source: sixth transfer program, 24 October 2026. The conditioning event is
actual simultaneous inclusion of finitely many orthonormal Q probes. Its
positive mass is proved from independence of their projected vectors.
The inverse-Gram correction remains a complete nonnegative projection norm.
A uniformly positive conditioning mass suffices for the moving-event RH iff;
no unproved membership of the other probes in the legal span is used.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical Topology
namespace RiemannResearch.RH.QRamanujanDPP
open Pareto ZetaTwoHilbert QRamanujanCanonicalOptimizer
open RiemannResearch.Probability.DPP
open RiemannResearch.Analysis.FiniteHilbertGram

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def projectedHead (e : Option ι → QHilbert) (n : ℕ) (i : ι) : QHilbert :=
  (QFullResidueProjection.stage n).starProjection (e (some i))

def headMass (e : Option ι → QHilbert)
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0) (n : ℕ) : ℝ :=
  (probeLaw e he n).real {x | ∀ i, x (some i) = true}

def conditionedVacancy (e : Option ι → QHilbert)
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0) (n : ℕ) : ℝ :=
  (probeLaw e he n).real {x | (∀ i, x (some i) = true) ∧ x none = false} / headMass e he n

def conditioningCost (e : Option ι → QHilbert) (n : ℕ) : ℝ :=
  ‖(synthesisSpan (projectedHead e n)).starProjection
    ((QFullResidueProjection.stage n).starProjection qOne)‖ ^ 2

theorem headMass_eq_gramDet (e : Option ι → QHilbert)
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0) (n : ℕ) :
    headMass e he n = (gramMatrix (projectedHead e n)).det :=
  (probeLaw_isDPP e he n).option_head_inclusion

theorem headMass_pos (e : Option ι → QHilbert)
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0) (n : ℕ)
    (hi : LinearIndependent ℝ (projectedHead e n)) : 0 < headMass e he n := by
  rw [headMass_eq_gramDet]
  exact gramMatrix_det_pos hi

theorem projectedHead_independent_of_headMass_pos (e : Option ι → QHilbert)
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0) (n : ℕ)
    (hp : 0 < headMass e he n) : LinearIndependent ℝ (projectedHead e n) := by
  apply Matrix.linearIndependent_of_det_gram_ne_zero
  change (gramMatrix (projectedHead e n)).det ≠ 0
  rw [← headMass_eq_gramDet e he n]
  exact ne_of_gt hp

/-- The source cost is an actual projected Hilbert norm, equal to its full inverse-Gram form. -/
theorem conditioningCost_inverseGram (e : Option ι → QHilbert) (n : ℕ)
    (hi : LinearIndependent ℝ (projectedHead e n)) :
    conditioningCost e n = dotProduct
      (cross (projectedHead e n) ((QFullResidueProjection.stage n).starProjection qOne))
      ((gramMatrix (projectedHead e n))⁻¹.mulVec
        (cross (projectedHead e n) ((QFullResidueProjection.stage n).starProjection qOne))) := by
  rw [conditioningCost, ← real_inner_self_eq_norm_sq]
  exact projection_inner_eq_inverseGram hi _ _

/-- Exact conditional target vacancy: canonical defect plus the complete signed source capacity. -/
theorem conditionedVacancy_eq (e : Option ι → QHilbert)
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0)
    (ht : e none = qOne) (n : ℕ) (hi : LinearIndependent ℝ (projectedHead e n)) :
    conditionedVacancy e he n = packetError n + conditioningCost e n := by
  have hh := (probeLaw_isDPP e he n).option_conditioned_vacancy_schur
    (headMass_pos e he n hi)
  have hc : (∑ i, probeKernel e n none (some i) *
      (∑ j, ((Matrix.of (fun i j => probeKernel e n (some i) (some j)))⁻¹) i j *
        probeKernel e n (some j) none)) = conditioningCost e n := by
    have hg : Matrix.of (fun i j => probeKernel e n (some i) (some j)) =
        gramMatrix (projectedHead e n) := by
      ext i j
      rfl
    have hb (j : ι) : probeKernel e n (some j) none =
        cross (projectedHead e n) ((QFullResidueProjection.stage n).starProjection qOne) j := by
      simp only [probeKernel, Matrix.of_apply, RiemannResearch.Analysis.ProjectionDPP.kernel,
        projectedHead, cross, ht]
    rw [conditioningCost_inverseGram e n hi]
    simp only [Matrix.mulVec, dotProduct, hg, hb]
    apply Finset.sum_congr rfl
    intro i _
    have hs : probeKernel e n none (some i) =
        cross (projectedHead e n) ((QFullResidueProjection.stage n).starProjection qOne) i := by
      change inner ℝ ((QFullResidueProjection.stage n).starProjection (e none))
          ((QFullResidueProjection.stage n).starProjection (e (some i))) =
        inner ℝ ((QFullResidueProjection.stage n).starProjection (e (some i)))
          ((QFullResidueProjection.stage n).starProjection qOne)
      rw [ht]
      exact real_inner_comm _ _
    rw [hs]
  rw [probe_target_diagonal e none ht n, hc] at hh
  simpa only [Set.mem_ofPred_eq, Bool.not_eq_true, conditionedVacancy, headMass, packetError] using hh

theorem conditionedVacancy_bounds (e : Option ι → QHilbert)
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0)
    (ht : e none = qOne) (n : ℕ) (hi : LinearIndependent ℝ (projectedHead e n)) :
    packetError n ≤ conditionedVacancy e he n ∧
      conditionedVacancy e he n ≤ packetError n / headMass e he n := by
  constructor
  · rw [conditionedVacancy_eq e he ht n hi]
    exact le_add_of_nonneg_right (sq_nonneg _)
  · have hm : (probeLaw e he n).real
        {x | (∀ i, x (some i) = true) ∧ x none = false} ≤
        (probeLaw e he n).real {x | x none = false} :=
      measureReal_mono (fun x hx => hx.2)
    rw [probe_target_vacancy e he none ht n] at hm
    exact div_le_div_of_nonneg_right hm (headMass_pos e he n hi).le

/-- Moving finite tests with conditioning mass bounded away from zero give an RH iff.
The only RH converse input is the explicit open Baez--Duarte provider. -/
theorem moving_conditioned_vacancy_iff_rh
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation)
    {α : Type*} {l : Filter α} [NeBot l] (N : α → ℕ) (hN : Tendsto N l atTop)
    (e : α → Option ι → QHilbert)
    (he : ∀ a i j, inner ℝ (e a i) (e a j) = if i = j then 1 else 0)
    (ht : ∀ a, e a none = qOne)
    (δ : ℝ) (hδ : 0 < δ)
    (hp : ∀ᶠ a in l, δ ≤ headMass (e a) (he a) (N a)) :
    Tendsto (fun a => conditionedVacancy (e a) (he a) (N a)) l (𝓝 0) ↔
      RiemannHypothesis := by
  have hlim : Tendsto (fun a => packetError (N a)) l (𝓝 packetLimitEnergy) := by
    simpa only [Function.comp_def] using packetError_tendsto.comp hN
  have hbound : ∀ᶠ a in l,
      packetError (N a) ≤ conditionedVacancy (e a) (he a) (N a) ∧
      conditionedVacancy (e a) (he a) (N a) ≤
        packetError (N a) / headMass (e a) (he a) (N a) := by
    filter_upwards [hp] with a ha
    exact conditionedVacancy_bounds (e a) (he a) (ht a) (N a)
      (projectedHead_independent_of_headMass_pos (e a) (he a) (N a) (lt_of_lt_of_le hδ ha))
  constructor
  · intro hc
    have hz : Tendsto (fun a => packetError (N a)) l (𝓝 0) :=
      squeeze_zero' (Filter.Eventually.of_forall (fun a => (packetError_pos (N a)).le))
        (hbound.mono (fun _ ha => ha.1)) hc
    exact (packetLimitEnergy_zero_iff_rh hBaezDuarte).mp (tendsto_nhds_unique hlim hz)
  · intro hrh
    have hz : Tendsto (fun a => packetError (N a)) l (𝓝 0) := by
      simpa only [(packetLimitEnergy_zero_iff_rh hBaezDuarte).mpr hrh] using hlim
    apply squeeze_zero' (hbound.mono (fun a ha => (packetError_pos (N a)).le.trans ha.1))
    · filter_upwards [hp, hbound] with a ha hb
      exact hb.2.trans
        (div_le_div_of_nonneg_left (packetError_pos (N a)).le hδ ha)
    · simpa only [zero_div] using hz.div_const δ

/-- Legal orthonormal conditioning probes have asymptotically full head-inclusion mass.
Only the head probes are required to belong to the closure; the target is not. -/
theorem headMass_tendsto_one_of_mem (e : Option ι → QHilbert)
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0)
    (hm : ∀ i, e (some i) ∈ QFullResidueProjection.closure) :
    Tendsto (headMass e he) atTop (𝓝 1) := by
  change Tendsto (fun n => headMass e he n) atTop (𝓝 1)
  have hproj (i : ι) : Tendsto (fun n => projectedHead e n i) atTop (𝓝 (e (some i))) := by
    have h := RiemannResearch.Analysis.ExhaustiveWalk.walkProjection_tendsto
      (fun i => qResidue (i + 2)) id Function.surjective_id (e (some i))
    change Tendsto (fun n => projectedHead e n i) atTop
      (𝓝 (QFullResidueProjection.closure.starProjection (e (some i)))) at h
    simpa only [Submodule.starProjection_eq_self_iff.mpr (hm i)] using h
  have hg : Tendsto (fun n => gramMatrix (projectedHead e n)) atTop (𝓝 (1 : Matrix ι ι ℝ)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    have hij : Tendsto (fun n => inner ℝ (projectedHead e n i) (projectedHead e n j))
        atTop (𝓝 (inner ℝ (e (some i)) (e (some j)))) := (hproj i).inner (hproj j)
    simpa only [gramMatrix, Matrix.of_apply, he, Option.some.injEq, Matrix.one_apply] using hij
  have hd := (continuous_id.matrix_det.tendsto (1 : Matrix ι ι ℝ)).comp hg
  simpa only [Function.comp_def, id_eq, headMass_eq_gramDet, Matrix.det_one] using hd

/-- Fixed legal conditioning preserves the entire limiting target defect,
unconditionally; this is stronger than just a zero-limit equivalence. -/
theorem fixed_conditioned_vacancy_tendsto (e : Option ι → QHilbert)
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0)
    (ht : e none = qOne) (hm : ∀ i, e (some i) ∈ QFullResidueProjection.closure) :
    Tendsto (conditionedVacancy e he) atTop (𝓝 packetLimitEnergy) := by
  have hmass := headMass_tendsto_one_of_mem e he hm
  have hp : ∀ᶠ n in atTop, 0 < headMass e he n :=
    hmass.eventually_const_lt (by norm_num : (0 : ℝ) < 1)
  have hb : ∀ᶠ n in atTop,
      packetError n ≤ conditionedVacancy e he n ∧
        conditionedVacancy e he n ≤ packetError n / headMass e he n := by
    filter_upwards [hp] with n hn
    exact conditionedVacancy_bounds e he ht n
      (projectedHead_independent_of_headMass_pos e he n hn)
  have hu : Tendsto (fun n => packetError n / headMass e he n - packetError n)
      atTop (𝓝 0) := by
    simpa only [Pi.div_apply, div_one, sub_self] using
      (packetError_tendsto.div hmass (by norm_num : (1 : ℝ) ≠ 0)).sub packetError_tendsto
  have hc : Tendsto (fun n => conditionedVacancy e he n - packetError n)
      atTop (𝓝 0) := squeeze_zero'
    (hb.mono (fun _ hn => sub_nonneg.mpr hn.1))
    (hb.mono (fun n hn => sub_le_sub_right hn.2 (packetError n))) hu
  simpa only [sub_add_cancel, zero_add] using hc.add packetError_tendsto

/-- For any fixed legal orthonormal head, positivity and rank hypotheses are
derived eventually. Thus no uniform-probability assumption remains. -/
theorem fixed_conditioned_vacancy_iff_rh
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation)
    (e : Option ι → QHilbert)
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0)
    (ht : e none = qOne) (hm : ∀ i, e (some i) ∈ QFullResidueProjection.closure) :
    Tendsto (conditionedVacancy e he) atTop (𝓝 0) ↔ RiemannHypothesis := by
  have hc := fixed_conditioned_vacancy_tendsto e he ht hm
  have hh : Tendsto (conditionedVacancy e he) atTop (𝓝 0) ↔ packetLimitEnergy = 0 := by
    constructor
    · exact fun h => tendsto_nhds_unique hc h
    · intro h
      simpa only [h] using hc
  exact hh.trans (packetLimitEnergy_zero_iff_rh hBaezDuarte)

end RiemannResearch.RH.QRamanujanDPP
