import RiemannResearch.Analysis.WeightedCoordinateTopology
import RiemannResearch.RH.RamanujanAdmissibleWeights
import Lean.Elab.Tactic.Omega

/-!
# Bounded-family topology of actual dual conductor coordinates

Source: sixth Ramanujan transfer program, 24 October 2026. Arbitrary bounded
physical families are allowed; no normal equations, legality, canonical
projection, or cofinality assumption is imposed in these topology results.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.RamanujanCoordinateTopology
open Pareto ZetaTwoHilbert RamanujanWeightedDefect
open RiemannResearch.Analysis.WeightedCoordinateEnergy
open RiemannResearch.Analysis.WeightedCoordinateTopology

theorem pareto_energy_zero_iff_conductors
    {α : Type*} {l : Filter α} (w : ℕ → ℝ) (hw : ∀ j, 0 < w j)
    (hs : Summable (fun j => w j * ‖paretoCoordinates j‖ ^ 2))
    (F : α → ThresholdHilbert) (x : ThresholdHilbert) (B : ℝ)
    (hbound : ∀ᶠ i in l, ‖F i - x‖ ^ 2 ≤ B) :
    Tendsto (fun i => observationEnergy w paretoCoordinates (F i - x)) l (𝓝 0) ↔
      ∀ m : ℕ, 1 < m → Tendsto
        (fun i => CoefficientStabilization.coefficientCLM m (F i)) l
        (𝓝 (CoefficientStabilization.coefficientCLM m x)) := by
  rw [energy_zero_iff_coordinates w paretoCoordinates hw hs F x B hbound]
  constructor
  · intro h m hm
    have he : m - 2 + 2 = m := by omega
    simpa only [paretoCoordinates, he] using h (m - 2)
  · intro h j
    exact h (j + 2) (by omega)

theorem q_energy_zero_iff_conductors
    {α : Type*} {l : Filter α} (w : ℕ → ℝ) (hw : ∀ j, 0 < w j)
    (hs : Summable (fun j => w j * ‖qCoordinates j‖ ^ 2))
    (F : α → QHilbert) (x : QHilbert) (B : ℝ)
    (hbound : ∀ᶠ i in l, ‖F i - x‖ ^ 2 ≤ B) :
    Tendsto (fun i => observationEnergy w qCoordinates (F i - x)) l (𝓝 0) ↔
      ∀ m : ℕ, 1 < m → Tendsto (fun i => SquarefreeMobiusProjection.qCoefficientCLM m (F i)) l (𝓝 (SquarefreeMobiusProjection.qCoefficientCLM m x)) := by
  rw [energy_zero_iff_coordinates w qCoordinates hw hs F x B hbound]
  constructor
  · intro h m hm
    have he : m - 2 + 2 = m := by omega
    simpa only [qCoordinates, he] using h (m - 2)
  · intro h j
    exact h (j + 2) (by omega)

/-- Any positive admissible weighting can be replaced by the explicit
geometric normalization on the same bounded actual Pareto family. -/
theorem pareto_weight_independence
    {α : Type*} {l : Filter α} (w : ℕ → ℝ) (hw : ∀ j, 0 < w j)
    (hs : Summable (fun j => w j * ‖paretoCoordinates j‖ ^ 2))
    (F : α → ThresholdHilbert) (x : ThresholdHilbert) (B : ℝ)
    (hbound : ∀ᶠ i in l, ‖F i - x‖ ^ 2 ≤ B) :
    Tendsto (fun i => observationEnergy w paretoCoordinates (F i - x)) l (𝓝 0) ↔
      Tendsto (fun i => energy paretoCoordinates (F i - x)) l (𝓝 0) :=
  positive_weights_same_bounded_topology w (weight paretoCoordinates) paretoCoordinates
    hw (weight_pos paretoCoordinates) hs (geometric_weight_moment_summable paretoCoordinates)
    F x B hbound

theorem q_weight_independence
    {α : Type*} {l : Filter α} (w : ℕ → ℝ) (hw : ∀ j, 0 < w j)
    (hs : Summable (fun j => w j * ‖qCoordinates j‖ ^ 2))
    (F : α → QHilbert) (x : QHilbert) (B : ℝ)
    (hbound : ∀ᶠ i in l, ‖F i - x‖ ^ 2 ≤ B) :
    Tendsto (fun i => observationEnergy w qCoordinates (F i - x)) l (𝓝 0) ↔
      Tendsto (fun i => energy qCoordinates (F i - x)) l (𝓝 0) :=
  positive_weights_same_bounded_topology w (weight qCoordinates) qCoordinates
    hw (weight_pos qCoordinates) hs (geometric_weight_moment_summable qCoordinates)
    F x B hbound

end RiemannResearch.RH.RamanujanCoordinateTopology
