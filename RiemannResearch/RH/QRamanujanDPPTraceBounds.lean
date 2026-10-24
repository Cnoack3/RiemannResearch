import RiemannResearch.RH.QRamanujanDPPConditioning
import RiemannResearch.RH.QRamanujanDPPVolume
import RiemannResearch.Probability.DeterminantalInclusionBounds
import RiemannResearch.LinearAlgebra.DeterminantTraceBounds
import RiemannResearch.Analysis.ProjectionDPPKernel
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Trace budgets and growing conditioning heads in actual Q

Source: user-provided finite inclusion bound, 24 October 2026, and its
spectral refinement. The full complementary Gram identity retains every
signed off-diagonal term. These unconditional finite estimates do not
establish the arithmetic hypotheses for arbitrary growing legal probes.
The growing-head RH reduction explicitly retains the open Baez--Duarte provider.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical Topology
namespace RiemannResearch.RH.QRamanujanDPP
open Pareto ZetaTwoHilbert QRamanujanCanonicalOptimizer
open RiemannResearch.Probability.DPP
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.ProjectionDPP
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def headLoss (e : Option ι → QHilbert) (n : ℕ) : ℝ :=
  ∑ i, ‖e (some i) - projectedHead e n i‖ ^ 2
theorem headLoss_eq_trace_defect (e : Option ι → QHilbert)
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0) (n : ℕ) :
    headLoss e n = (1 - gramMatrix (projectedHead e n)).trace := by
  unfold headLoss Matrix.trace
  apply Finset.sum_congr rfl
  intro i _
  have hh := RiemannResearch.Analysis.ProjectionDPP.holeKernel_eq (QFullResidueProjection.stage n) e (some i) (some i)
  rw [RiemannResearch.Analysis.ProjectionDPP.holeKernel_diagonal, he] at hh
  simpa only [if_true, Matrix.diag, Matrix.sub_apply, Matrix.one_apply_eq,
    gramMatrix, Matrix.of_apply, projectedHead, RiemannResearch.Analysis.ProjectionDPP.kernel] using hh
theorem headMass_lower_bound_loss (e : Option ι → QHilbert)
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0) (n : ℕ) :
    1 - headLoss e n ≤ headMass e he n := by
  have hh := (probeLaw_isDPP e he n).det_lower_bound_trace_defect
    (⟨some, fun _ _ h => Option.some.inj h⟩ : ι ↪ Option ι)
  rw [headLoss_eq_trace_defect e he n, headMass_eq_gramDet]
  exact hh
theorem headMass_ge_of_loss_le (e : Option ι → QHilbert)
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0) (n : ℕ)
    {δ : ℝ} (h : headLoss e n ≤ 1 - δ) : δ ≤ headMass e he n := by
  have hh := headMass_lower_bound_loss e he n
  linarith
theorem headMass_eq_one_of_mem_stage (e : Option ι → QHilbert)
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0) (n : ℕ)
    (hm : ∀ i, e (some i) ∈ QFullResidueProjection.stage n) :
    headMass e he n = 1 := by
  rw [headMass_eq_gramDet]
  have hg : gramMatrix (projectedHead e n) = 1 := by
    ext i j
    simp only [gramMatrix, Matrix.of_apply, projectedHead,
      Submodule.starProjection_eq_self_iff.mpr (hm i),
      Submodule.starProjection_eq_self_iff.mpr (hm j),
      he, Option.some.injEq, Matrix.one_apply]
  rw [hg, Matrix.det_one]

/-- The entire defect matrix, including signed off-diagonal entries, is a Gram matrix. -/
theorem headDefect_eq_residualGram (e : Option ι → QHilbert)
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0) (n : ℕ) :
    1 - gramMatrix (projectedHead e n) =
      gramMatrix (fun i => e (some i) - projectedHead e n i) := by
  ext i j
  have hh := RiemannResearch.Analysis.ProjectionDPP.holeKernel_eq
    (QFullResidueProjection.stage n) e (some i) (some j)
  simpa only [Matrix.sub_apply, Matrix.one_apply, gramMatrix, projectedHead,
    RiemannResearch.Analysis.ProjectionDPP.holeKernel,
    RiemannResearch.Analysis.ProjectionDPP.kernel, he, Option.some.injEq] using hh.symm

theorem headLoss_eq_sum_vacancies (e : Option ι → QHilbert)
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0) (n : ℕ) :
    headLoss e n = ∑ i, (probeLaw e he n).real {x | x (some i) = false} := by
  unfold headLoss
  apply Finset.sum_congr rfl
  intro i _
  have hh := RiemannResearch.Analysis.ProjectionDPP.holeKernel_eq
    (QFullResidueProjection.stage n) e (some i) (some i)
  rw [RiemannResearch.Analysis.ProjectionDPP.holeKernel_diagonal, he] at hh
  have hv := (probeLaw_isDPP e he n).vacancy (some i)
  calc
    _ = 1 - probeKernel e n (some i) (some i) := by
      simpa only [if_true, projectedHead, probeKernel, Matrix.of_apply] using hh
    _ = _ := by simpa only [Set.mem_ofPred_eq, Bool.not_eq_true] using hv.symm

theorem headMass_eq_zero_of_card_gt_stage (e : Option ι → QHilbert)
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0) (n : ℕ)
    (hcard : n < Fintype.card ι) : headMass e he n = 0 := by
  rw [headMass_eq_gramDet]
  by_contra hd
  let v : ι → QFullResidueProjection.stage n := fun i =>
    ⟨projectedHead e n i, (QFullResidueProjection.stage n).starProjection_apply_mem _⟩
  have hv : LinearIndependent ℝ v := Matrix.linearIndependent_of_det_gram_ne_zero (by
    change (gramMatrix (projectedHead e n)).det ≠ 0
    exact hd)
  have hc := hv.fintype_card_le_finrank
  rw [stage_finrank] at hc
  exact (not_lt_of_ge hc) hcard

theorem headLoss_le_card_mul (e : Option ι → QHilbert) (n : ℕ) {η : ℝ}
    (h : ∀ i, ‖e (some i) - projectedHead e n i‖ ^ 2 ≤ η) :
    headLoss e n ≤ (Fintype.card ι : ℝ) * η := by
  calc
    headLoss e n ≤ ∑ _i : ι, η := Finset.sum_le_sum (fun i _ => h i)
    _ = _ := by simp

/-- Unlike Transfer 100, the auxiliary cardinality may vary with the parameter. -/
theorem growing_conditioned_vacancy_iff_rh
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation)
    {α : Type*} {l : Filter α} [NeBot l] (N : α → ℕ) (hN : Tendsto N l atTop)
    (m : α → ℕ) (e : ∀ a, Option (Fin (m a)) → QHilbert)
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
      (projectedHead_independent_of_headMass_pos (e a) (he a) (N a)
        (lt_of_lt_of_le hδ ha))
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
      exact hb.2.trans (div_le_div_of_nonneg_left (packetError_pos (N a)).le hδ ha)
    · simpa only [zero_div] using hz.div_const δ

theorem growing_conditioned_vacancy_iff_rh_of_trace_budget
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation)
    {α : Type*} {l : Filter α} [NeBot l] (N : α → ℕ) (hN : Tendsto N l atTop)
    (m : α → ℕ) (e : ∀ a, Option (Fin (m a)) → QHilbert)
    (he : ∀ a i j, inner ℝ (e a i) (e a j) = if i = j then 1 else 0)
    (ht : ∀ a, e a none = qOne)
    (δ : ℝ) (hδ : 0 < δ)
    (hloss : ∀ᶠ a in l, headLoss (e a) (N a) ≤ 1 - δ) :
    Tendsto (fun a => conditionedVacancy (e a) (he a) (N a)) l (𝓝 0) ↔
      RiemannHypothesis :=
  growing_conditioned_vacancy_iff_rh hBaezDuarte N hN m e he ht δ hδ
    (hloss.mono (fun a ha => headMass_ge_of_loss_le (e a) (he a) (N a) ha))


theorem headGram_posSemidef (e : Option ι → QHilbert) (n : ℕ) :
    (gramMatrix (projectedHead e n)).PosSemidef :=
  Matrix.posSemidef_gram ℝ (projectedHead e n)

theorem headDefect_posSemidef (e : Option ι → QHilbert)
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0) (n : ℕ) :
    (1 - gramMatrix (projectedHead e n)).PosSemidef := by
  rw [headDefect_eq_residualGram e he n]
  exact Matrix.posSemidef_gram ℝ (fun i : ι => e (some i) - projectedHead e n i)

theorem headMass_exp_lower_bound (e : Option ι → QHilbert)
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0) (n : ℕ)
    {ε : ℝ} (hε : 0 < ε)
    (hgap : ∀ i, ε ≤ (headGram_posSemidef e n).isHermitian.eigenvalues i) :
    Real.exp (-headLoss e n / ε) ≤ headMass e he n := by
  rw [headLoss_eq_trace_defect e he n, headMass_eq_gramDet]
  exact (headGram_posSemidef e n).exp_neg_trace_defect_div_le_det
    (headDefect_posSemidef e he n) hε hgap

theorem headMass_exp_upper_bound (e : Option ι → QHilbert)
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0) (n : ℕ) :
    headMass e he n ≤ Real.exp (-headLoss e n) := by
  rw [headLoss_eq_trace_defect e he n, headMass_eq_gramDet]
  exact (headGram_posSemidef e n).det_le_exp_neg_trace_defect


/-- Exact actual-Q mass identity, retaining every spectral chord remainder. -/
theorem headMass_eq_exp_trace_chord_add_gap (e : Option ι → QHilbert)
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0) (n : ℕ)
    {ε : ℝ} (hε : 0 < ε)
    (hgap : ∀ i, ε ≤ (headGram_posSemidef e n).isHermitian.eigenvalues i) :
    headMass e he n = Real.exp (headLoss e n / (1 - ε) * Real.log ε +
      ∑ i, RiemannResearch.LinearAlgebra.DeterminantTrace.logChordGap
        ε ((headGram_posSemidef e n).isHermitian.eigenvalues i)) := by
  rw [headLoss_eq_trace_defect e he n, headMass_eq_gramDet]
  exact (headGram_posSemidef e n).det_eq_exp_trace_chord_add_gap hε hgap

/-- The sharper gap/trace lower bound for genuine Q conditioning mass. -/
theorem headMass_chord_lower_bound (e : Option ι → QHilbert)
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0) (n : ℕ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hgap : ∀ i, ε ≤ (headGram_posSemidef e n).isHermitian.eigenvalues i) :
    Real.exp (headLoss e n / (1 - ε) * Real.log ε) ≤ headMass e he n := by
  rw [headLoss_eq_trace_defect e he n, headMass_eq_gramDet]
  exact (headGram_posSemidef e n).exp_trace_chord_le_det
    (headDefect_posSemidef e he n) hε hε1 hgap

/-- Explicit conditioning amplification with the improved mass constant. -/
theorem conditionedVacancy_le_chord (e : Option ι → QHilbert)
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0)
    (ht : e none = qOne) (n : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hgap : ∀ i, ε ≤ (headGram_posSemidef e n).isHermitian.eigenvalues i) :
    conditionedVacancy e he n ≤
      Real.exp (-(headLoss e n / (1 - ε) * Real.log ε)) * packetError n := by
  have hm := headMass_chord_lower_bound e he n hε hε1 hgap
  have hi := projectedHead_independent_of_headMass_pos e he n
    ((Real.exp_pos _).trans_le hm)
  calc
    conditionedVacancy e he n ≤ packetError n / headMass e he n :=
      (conditionedVacancy_bounds e he ht n hi).2
    _ ≤ packetError n / Real.exp (headLoss e n / (1 - ε) * Real.log ε) :=
      div_le_div_of_nonneg_left (packetError_pos n).le (Real.exp_pos _) hm
    _ = _ := by rw [div_eq_mul_inv, ← Real.exp_neg]; ring

theorem headMass_trace_gap_iff
    {α : Type*} {l : Filter α} (m N : α → ℕ)
    (e : ∀ a, Option (Fin (m a)) → QHilbert)
    (he : ∀ a i j, inner ℝ (e a i) (e a j) = if i = j then 1 else 0) :
    (∃ δ : ℝ, 0 < δ ∧ ∀ᶠ a in l, δ ≤ headMass (e a) (he a) (N a)) ↔
      ∃ C ε : ℝ, 0 < ε ∧ ∀ᶠ a in l,
        headLoss (e a) (N a) ≤ C ∧
        ∀ i, ε ≤ (headGram_posSemidef (e a) (N a)).isHermitian.eigenvalues i := by
  simpa only [headMass_eq_gramDet, headLoss_eq_trace_defect _ (he _) _] using
    Matrix.uniform_det_pos_iff_trace_bound_and_gap
      (fun a => Fin (m a)) (fun a => gramMatrix (projectedHead (e a) (N a)))
      (fun a => headGram_posSemidef (e a) (N a))
      (fun a => headDefect_posSemidef (e a) (he a) (N a))

end RiemannResearch.RH.QRamanujanDPP
