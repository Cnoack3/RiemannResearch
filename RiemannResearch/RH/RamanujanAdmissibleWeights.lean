import RiemannResearch.Analysis.WeightedCoordinateEnergy
import RiemannResearch.RH.RamanujanWeightedDefect

/-!
# Arbitrary admissible weights for Ramanujan coefficient defects

Source: independently developed weighted-observation extension of the
verified scalar-defect criterion, sixth transfer program, 24 October 2026.
Every strictly positive weight family with a finite weighted operator-norm
moment gives the same saturation criterion. No rate or summability of the
unweighted coefficient array is assumed. RH converses retain the Open
Baez--Duarte natural-approximation provider.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.RamanujanAdmissibleWeights
open Pareto ZetaTwoHilbert RamanujanWeightedDefect
open RiemannResearch.Analysis.WeightedCoordinateEnergy

def paretoDefectWith (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  observationEnergy w paretoCoordinates (hilbertOne - CoefficientStabilization.projection n)

def qDefectWith (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  observationEnergy w qCoordinates (qOne - QRamanujanCanonicalOptimizer.packetCandidate n)

def paretoLimitWith (w : ℕ → ℝ) : ℝ :=
  observationEnergy w paretoCoordinates CoefficientStabilization.limitResidual

def qLimitWith (w : ℕ → ℝ) : ℝ :=
  observationEnergy w qCoordinates (qOne - QFullResidueProjection.closure.starProjection qOne)

theorem paretoDefectWith_series (w : ℕ → ℝ) (n : ℕ) :
    paretoDefectWith w n = ∑' j, w j *
      (RamanujanCanonicalOptimizer.packetMultipleCoefficient n (j + 2) +
        (ArithmeticFunction.moebius (j + 2) : ℝ)) ^ 2 := by
  simp only [paretoDefectWith, observationEnergy, pareto_coordinate_residual, neg_sq]

theorem qDefectWith_series (w : ℕ → ℝ) (n : ℕ) :
    qDefectWith w n = ∑' j, w j *
      (QRamanujanCanonicalOptimizer.packetCoordinate n (j + 2) +
        (ArithmeticFunction.moebius (j + 2) : ℝ)) ^ 2 := by
  simp only [qDefectWith, observationEnergy, q_coordinate_residual, neg_sq]

theorem paretoDefectWith_tendsto (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hs : Summable (fun j => w j * ‖paretoCoordinates j‖ ^ 2)) :
    Tendsto (paretoDefectWith w) atTop (𝓝 (paretoLimitWith w)) := by
  apply observationEnergy_tendsto w paretoCoordinates hw hs
    (fun n => hilbertOne - CoefficientStabilization.projection n)
    CoefficientStabilization.limitResidual
  · intro j
    exact ((paretoCoordinates j).continuous.tendsto _).comp
      (tendsto_const_nhds.sub CoefficientStabilization.projection_tendsto)
  · exact Eventually.of_forall pareto_residual_bound

theorem qDefectWith_tendsto (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hs : Summable (fun j => w j * ‖qCoordinates j‖ ^ 2)) :
    Tendsto (qDefectWith w) atTop (𝓝 (qLimitWith w)) := by
  apply observationEnergy_tendsto w qCoordinates hw hs
    (fun n => qOne - QRamanujanCanonicalOptimizer.packetCandidate n)
    (qOne - QFullResidueProjection.closure.starProjection qOne)
  · intro j
    exact ((qCoordinates j).continuous.tendsto _).comp
      (tendsto_const_nhds.sub QRamanujanCanonicalOptimizer.packetCandidate_tendsto_projection)
  · exact Eventually.of_forall q_residual_bound

theorem paretoLimitWith_zero_iff (w : ℕ → ℝ) (hw : ∀ j, 0 < w j)
    (hs : Summable (fun j => w j * ‖paretoCoordinates j‖ ^ 2)) :
    paretoLimitWith w = 0 ↔ CoefficientStabilization.limitEnergy = 0 := by
  have h := paretoLimitDefect_zero_iff
  rw [paretoLimitDefect, energy_eq_zero_iff] at h
  rw [paretoLimitWith, observationEnergy_eq_zero_iff w paretoCoordinates hw hs]
  exact h

theorem qLimitWith_zero_iff (w : ℕ → ℝ) (hw : ∀ j, 0 < w j)
    (hs : Summable (fun j => w j * ‖qCoordinates j‖ ^ 2)) :
    qLimitWith w = 0 ↔ QRamanujanCanonicalOptimizer.packetLimitEnergy = 0 := by
  have h := qLimitDefect_zero_iff
  rw [qLimitDefect, energy_eq_zero_iff] at h
  rw [qLimitWith, observationEnergy_eq_zero_iff w qCoordinates hw hs]
  exact h

theorem paretoDefectWith_cofinal_zero_iff (w : ℕ → ℝ) (hw : ∀ j, 0 < w j)
    (hs : Summable (fun j => w j * ‖paretoCoordinates j‖ ^ 2))
    {α : Type*} {l : Filter α} [NeBot l] (N : α → ℕ) (hN : Tendsto N l atTop) :
    Tendsto (fun i => paretoDefectWith w (N i)) l (𝓝 0) ↔
      CoefficientStabilization.limitEnergy = 0 := by
  rw [← paretoLimitWith_zero_iff w hw hs]
  constructor
  · intro h
    exact tendsto_nhds_unique ((paretoDefectWith_tendsto w (fun j => (hw j).le) hs).comp hN) h
  · intro h
    simpa only [h, Function.comp_def] using
      (paretoDefectWith_tendsto w (fun j => (hw j).le) hs).comp hN

theorem qDefectWith_cofinal_zero_iff (w : ℕ → ℝ) (hw : ∀ j, 0 < w j)
    (hs : Summable (fun j => w j * ‖qCoordinates j‖ ^ 2))
    {α : Type*} {l : Filter α} [NeBot l] (N : α → ℕ) (hN : Tendsto N l atTop) :
    Tendsto (fun i => qDefectWith w (N i)) l (𝓝 0) ↔
      QRamanujanCanonicalOptimizer.packetLimitEnergy = 0 := by
  rw [← qLimitWith_zero_iff w hw hs]
  constructor
  · intro h
    exact tendsto_nhds_unique ((qDefectWith_tendsto w (fun j => (hw j).le) hs).comp hN) h
  · intro h
    simpa only [h, Function.comp_def] using
      (qDefectWith_tendsto w (fun j => (hw j).le) hs).comp hN

/-- Every admissible positive observation weighting yields the same pair of
scalar RH criteria. Weights and their summability requirements may differ
between the actual Pareto and Q spaces. -/
theorem admissible_weight_rh_equivalences
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation)
    (wP wQ : ℕ → ℝ) (hwP : ∀ j, 0 < wP j) (hwQ : ∀ j, 0 < wQ j)
    (hsP : Summable (fun j => wP j * ‖paretoCoordinates j‖ ^ 2))
    (hsQ : Summable (fun j => wQ j * ‖qCoordinates j‖ ^ 2))
    {α : Type*} {l : Filter α} [NeBot l] (N : α → ℕ) (hN : Tendsto N l atTop) :
    (Tendsto (fun i => paretoDefectWith wP (N i)) l (𝓝 0) ↔ RiemannHypothesis) ∧
      (Tendsto (fun i => qDefectWith wQ (N i)) l (𝓝 0) ↔ RiemannHypothesis) := by
  have hp := (RamanujanCanonicalOptimizer.packet_cofinal_mass_iff N hN).symm.trans
    (RamanujanCanonicalOptimizer.packet_cofinal_rh_equivalences hBaezDuarte N hN).1
  have hq := (QRamanujanCanonicalOptimizer.packet_cofinal_mass_iff N hN).symm.trans
    (QRamanujanCanonicalOptimizer.packet_cofinal_rh_equivalences hBaezDuarte N hN).1
  exact ⟨(paretoDefectWith_cofinal_zero_iff wP hwP hsP N hN).trans hp,
    (qDefectWith_cofinal_zero_iff wQ hwQ hsQ N hN).trans hq⟩

end RiemannResearch.RH.RamanujanAdmissibleWeights
