import RiemannResearch.Analysis.MovingWeightedObservationEnergy
import RiemannResearch.RH.RamanujanAdmissibleWeights

/-!
# Adaptive signed weights for the actual Ramanujan coefficient defects

Source: sixth transfer program, 24 October 2026. Weights may vary with every
packet stage and may have signs at finite stages. One eventual summable
operator-norm majorant and positive limiting weights retain the complete
saturation criterion. The converse RH implication is explicitly conditional.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.RamanujanMovingWeights
open Pareto ZetaTwoHilbert RamanujanWeightedDefect RamanujanAdmissibleWeights
open RiemannResearch.Analysis.MovingWeightedObservationEnergy
variable {α : Type*} {l : Filter α}

theorem pareto_moving_weights_tendsto
    (W : α → ℕ → ℝ) (w : ℕ → ℝ)
    (hweight : ∀ j, Tendsto (fun i => W i j) l (𝓝 (w j)))
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (hs : Summable a)
    (hdom : ∀ᶠ i in l, ∀ j, |W i j| * ‖paretoCoordinates j‖ ^ 2 ≤ a j)
    (N : α → ℕ) (hN : Tendsto N l atTop) :
    Tendsto (fun i => paretoDefectWith (W i) (N i)) l (𝓝 (paretoLimitWith w)) := by
  apply moving_energy_tendsto W w paretoCoordinates hweight a ha hs hdom
    (fun i => hilbertOne - CoefficientStabilization.projection (N i))
    CoefficientStabilization.limitResidual
  · intro j
    exact ((paretoCoordinates j).continuous.tendsto _).comp
      ((tendsto_const_nhds.sub CoefficientStabilization.projection_tendsto).comp hN)
  · exact Eventually.of_forall (fun i => pareto_residual_bound (N i))

theorem q_moving_weights_tendsto
    (W : α → ℕ → ℝ) (w : ℕ → ℝ)
    (hweight : ∀ j, Tendsto (fun i => W i j) l (𝓝 (w j)))
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (hs : Summable a)
    (hdom : ∀ᶠ i in l, ∀ j, |W i j| * ‖qCoordinates j‖ ^ 2 ≤ a j)
    (N : α → ℕ) (hN : Tendsto N l atTop) :
    Tendsto (fun i => qDefectWith (W i) (N i)) l (𝓝 (qLimitWith w)) := by
  apply moving_energy_tendsto W w qCoordinates hweight a ha hs hdom
    (fun i => qOne - QRamanujanCanonicalOptimizer.packetCandidate (N i))
    (qOne - QFullResidueProjection.closure.starProjection qOne)
  · intro j
    exact ((qCoordinates j).continuous.tendsto _).comp
      ((tendsto_const_nhds.sub QRamanujanCanonicalOptimizer.packetCandidate_tendsto_projection).comp hN)
  · exact Eventually.of_forall (fun i => q_residual_bound (N i))

theorem pareto_moving_weights_zero_iff [NeBot l]
    (W : α → ℕ → ℝ) (w : ℕ → ℝ) (hw : ∀ j, 0 < w j)
    (hweight : ∀ j, Tendsto (fun i => W i j) l (𝓝 (w j)))
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (hs : Summable a)
    (hdom : ∀ᶠ i in l, ∀ j, |W i j| * ‖paretoCoordinates j‖ ^ 2 ≤ a j)
    (N : α → ℕ) (hN : Tendsto N l atTop) :
    Tendsto (fun i => paretoDefectWith (W i) (N i)) l (𝓝 0) ↔
      CoefficientStabilization.limitEnergy = 0 := by
  have hm := limit_moment_summable W w paretoCoordinates hweight (fun j => (hw j).le) a hs hdom
  rw [← paretoLimitWith_zero_iff w hw hm]
  have ht := pareto_moving_weights_tendsto W w hweight a ha hs hdom N hN
  constructor
  · exact fun h => tendsto_nhds_unique ht h
  · intro h
    simpa only [h] using ht

theorem q_moving_weights_zero_iff [NeBot l]
    (W : α → ℕ → ℝ) (w : ℕ → ℝ) (hw : ∀ j, 0 < w j)
    (hweight : ∀ j, Tendsto (fun i => W i j) l (𝓝 (w j)))
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (hs : Summable a)
    (hdom : ∀ᶠ i in l, ∀ j, |W i j| * ‖qCoordinates j‖ ^ 2 ≤ a j)
    (N : α → ℕ) (hN : Tendsto N l atTop) :
    Tendsto (fun i => qDefectWith (W i) (N i)) l (𝓝 0) ↔
      QRamanujanCanonicalOptimizer.packetLimitEnergy = 0 := by
  have hm := limit_moment_summable W w qCoordinates hweight (fun j => (hw j).le) a hs hdom
  rw [← qLimitWith_zero_iff w hw hm]
  have ht := q_moving_weights_tendsto W w hweight a ha hs hdom N hN
  constructor
  · exact fun h => tendsto_nhds_unique ht h
  · intro h
    simpa only [h] using ht

theorem pareto_moving_weights_rh_iff [NeBot l]
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation)
    (W : α → ℕ → ℝ) (w : ℕ → ℝ) (hw : ∀ j, 0 < w j)
    (hweight : ∀ j, Tendsto (fun i => W i j) l (𝓝 (w j)))
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (hs : Summable a)
    (hdom : ∀ᶠ i in l, ∀ j, |W i j| * ‖paretoCoordinates j‖ ^ 2 ≤ a j)
    (N : α → ℕ) (hN : Tendsto N l atTop) :
    Tendsto (fun i => paretoDefectWith (W i) (N i)) l (𝓝 0) ↔ RiemannHypothesis :=
  (pareto_moving_weights_zero_iff W w hw hweight a ha hs hdom N hN).trans
    ((RamanujanCanonicalOptimizer.packet_cofinal_mass_iff N hN).symm.trans
      (RamanujanCanonicalOptimizer.packet_cofinal_rh_equivalences hBaezDuarte N hN).1)

theorem q_moving_weights_rh_iff [NeBot l]
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation)
    (W : α → ℕ → ℝ) (w : ℕ → ℝ) (hw : ∀ j, 0 < w j)
    (hweight : ∀ j, Tendsto (fun i => W i j) l (𝓝 (w j)))
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (hs : Summable a)
    (hdom : ∀ᶠ i in l, ∀ j, |W i j| * ‖qCoordinates j‖ ^ 2 ≤ a j)
    (N : α → ℕ) (hN : Tendsto N l atTop) :
    Tendsto (fun i => qDefectWith (W i) (N i)) l (𝓝 0) ↔ RiemannHypothesis :=
  (q_moving_weights_zero_iff W w hw hweight a ha hs hdom N hN).trans
    ((QRamanujanCanonicalOptimizer.packet_cofinal_mass_iff N hN).symm.trans
      (QRamanujanCanonicalOptimizer.packet_cofinal_rh_equivalences hBaezDuarte N hN).1)

end RiemannResearch.RH.RamanujanMovingWeights
