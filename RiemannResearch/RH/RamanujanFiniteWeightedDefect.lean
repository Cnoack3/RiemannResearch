import RiemannResearch.Analysis.WeightedCoordinateTruncation
import RiemannResearch.RH.RamanujanAdmissibleWeights

/-!
# Finite computable conductor heads with independent packet stages

Source: sixth transfer program, 24 October 2026. The complete omitted
arithmetic tail is explicit, and head depth may tend to infinity at any
rate independent of the packet stage. The RH converses retain their Open
Baez--Duarte provider.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.RamanujanFiniteWeightedDefect
open Pareto ZetaTwoHilbert RamanujanWeightedDefect RamanujanAdmissibleWeights
open RiemannResearch.Analysis.WeightedCoordinateEnergy
open RiemannResearch.Analysis.WeightedCoordinateTruncation

def paretoHeadDefect (w : ℕ → ℝ) (J n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range J, w j *
    (RamanujanCanonicalOptimizer.packetMultipleCoefficient n (j + 2) +
      (ArithmeticFunction.moebius (j + 2) : ℝ)) ^ 2

def qHeadDefect (w : ℕ → ℝ) (J n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range J, w j *
    (QRamanujanCanonicalOptimizer.packetCoordinate n (j + 2) +
      (ArithmeticFunction.moebius (j + 2) : ℝ)) ^ 2

theorem pareto_head_full_interval (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hs : Summable (fun j => w j * ‖paretoCoordinates j‖ ^ 2)) (J n : ℕ) :
    paretoHeadDefect w J n ≤ paretoDefectWith w n ∧
      paretoDefectWith w n ≤ paretoHeadDefect w J n + tailMass w paretoCoordinates J := by
  have h := head_error_interval w paretoCoordinates hw hs J
    (hilbertOne - CoefficientStabilization.projection n)
  have hb := mul_le_mul_of_nonneg_left (pareto_residual_bound n)
    (tailMass_nonneg w paretoCoordinates hw J)
  simp only [headEnergy, pareto_coordinate_residual, neg_sq, mul_one] at h hb
  change paretoHeadDefect w J n ≤ paretoDefectWith w n ∧ _ at h
  exact ⟨h.1, h.2.trans (by
    dsimp only [paretoHeadDefect]
    exact add_le_add le_rfl hb)⟩

theorem q_head_full_interval (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hs : Summable (fun j => w j * ‖qCoordinates j‖ ^ 2)) (J n : ℕ) :
    qHeadDefect w J n ≤ qDefectWith w n ∧
      qDefectWith w n ≤ qHeadDefect w J n + tailMass w qCoordinates J := by
  have h := head_error_interval w qCoordinates hw hs J
    (qOne - QRamanujanCanonicalOptimizer.packetCandidate n)
  have hb := mul_le_mul_of_nonneg_left (q_residual_bound n)
    (tailMass_nonneg w qCoordinates hw J)
  simp only [headEnergy, q_coordinate_residual, neg_sq, mul_one] at h hb
  change qHeadDefect w J n ≤ qDefectWith w n ∧ _ at h
  exact ⟨h.1, h.2.trans (by
    dsimp only [qHeadDefect]
    exact add_le_add le_rfl hb)⟩

theorem pareto_head_cofinal_tendsto (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hs : Summable (fun j => w j * ‖paretoCoordinates j‖ ^ 2))
    {α : Type*} {l : Filter α} (J N : α → ℕ)
    (hJ : Tendsto J l atTop) (hN : Tendsto N l atTop) :
    Tendsto (fun i => paretoHeadDefect w (J i) (N i)) l (𝓝 (paretoLimitWith w)) := by
  have h := moving_head_tendsto w paretoCoordinates hw hs
    (fun i => hilbertOne - CoefficientStabilization.projection (N i)) J hJ 1
    (Eventually.of_forall (fun i => pareto_residual_bound (N i)))
    ((paretoDefectWith_tendsto w hw hs).comp hN)
  simpa only [headEnergy, paretoHeadDefect, pareto_coordinate_residual, neg_sq] using h

theorem q_head_cofinal_tendsto (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hs : Summable (fun j => w j * ‖qCoordinates j‖ ^ 2))
    {α : Type*} {l : Filter α} (J N : α → ℕ)
    (hJ : Tendsto J l atTop) (hN : Tendsto N l atTop) :
    Tendsto (fun i => qHeadDefect w (J i) (N i)) l (𝓝 (qLimitWith w)) := by
  have h := moving_head_tendsto w qCoordinates hw hs
    (fun i => qOne - QRamanujanCanonicalOptimizer.packetCandidate (N i)) J hJ 1
    (Eventually.of_forall (fun i => q_residual_bound (N i)))
    ((qDefectWith_tendsto w hw hs).comp hN)
  simpa only [headEnergy, qHeadDefect, q_coordinate_residual, neg_sq] using h

/-- Finite arithmetic observations alone give a scalar criterion, provided
both depths are cofinal; no coupling or quantitative growth law is needed. -/
theorem pareto_head_zero_iff_saturation (w : ℕ → ℝ) (hw : ∀ j, 0 < w j)
    (hs : Summable (fun j => w j * ‖paretoCoordinates j‖ ^ 2))
    {α : Type*} {l : Filter α} [NeBot l] (J N : α → ℕ)
    (hJ : Tendsto J l atTop) (hN : Tendsto N l atTop) :
    Tendsto (fun i => paretoHeadDefect w (J i) (N i)) l (𝓝 0) ↔
      CoefficientStabilization.limitEnergy = 0 := by
  rw [← paretoLimitWith_zero_iff w hw hs]
  have ht := pareto_head_cofinal_tendsto w (fun j => (hw j).le) hs J N hJ hN
  constructor
  · exact fun h => tendsto_nhds_unique ht h
  · intro h
    simpa only [h] using ht

theorem q_head_zero_iff_saturation (w : ℕ → ℝ) (hw : ∀ j, 0 < w j)
    (hs : Summable (fun j => w j * ‖qCoordinates j‖ ^ 2))
    {α : Type*} {l : Filter α} [NeBot l] (J N : α → ℕ)
    (hJ : Tendsto J l atTop) (hN : Tendsto N l atTop) :
    Tendsto (fun i => qHeadDefect w (J i) (N i)) l (𝓝 0) ↔
      QRamanujanCanonicalOptimizer.packetLimitEnergy = 0 := by
  rw [← qLimitWith_zero_iff w hw hs]
  have ht := q_head_cofinal_tendsto w (fun j => (hw j).le) hs J N hJ hN
  constructor
  · exact fun h => tendsto_nhds_unique ht h
  · intro h
    simpa only [h] using ht

theorem finite_head_rh_equivalences
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation)
    (wP wQ : ℕ → ℝ) (hwP : ∀ j, 0 < wP j) (hwQ : ∀ j, 0 < wQ j)
    (hsP : Summable (fun j => wP j * ‖paretoCoordinates j‖ ^ 2))
    (hsQ : Summable (fun j => wQ j * ‖qCoordinates j‖ ^ 2))
    {α : Type*} {l : Filter α} [NeBot l] (J N : α → ℕ)
    (hJ : Tendsto J l atTop) (hN : Tendsto N l atTop) :
    (Tendsto (fun i => paretoHeadDefect wP (J i) (N i)) l (𝓝 0) ↔ RiemannHypothesis) ∧
      (Tendsto (fun i => qHeadDefect wQ (J i) (N i)) l (𝓝 0) ↔ RiemannHypothesis) := by
  have hp := (RamanujanCanonicalOptimizer.packet_cofinal_mass_iff N hN).symm.trans
    (RamanujanCanonicalOptimizer.packet_cofinal_rh_equivalences hBaezDuarte N hN).1
  have hq := (QRamanujanCanonicalOptimizer.packet_cofinal_mass_iff N hN).symm.trans
    (QRamanujanCanonicalOptimizer.packet_cofinal_rh_equivalences hBaezDuarte N hN).1
  exact ⟨(pareto_head_zero_iff_saturation wP hwP hsP J N hJ hN).trans hp,
    (q_head_zero_iff_saturation wQ hwQ hsQ J N hJ hN).trans hq⟩

end RiemannResearch.RH.RamanujanFiniteWeightedDefect
