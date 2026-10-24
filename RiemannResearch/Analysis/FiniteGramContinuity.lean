import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import RiemannResearch.Analysis.FiniteHilbertConstraints
import RiemannResearch.Analysis.FiniteGramCapacity
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.MulAction

/-!
# Moving finite Gram families and sources

Source: user-requested fourth Ramanujan dual continuation, 23 October 2026.
This supplies continuity of the actual full inverse Gram metric when both
its finite observation family and its source vary. Only the limiting family
must be independent for the matrix formulas; no uniform inverse bound or
independence of every approximating family is assumed.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.FiniteGramContinuity
open FiniteHilbertGram FiniteHilbertConstraints FiniteGramCapacity

variable {ι H α : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {l : Filter α}

/-- The total matrix formula, defined also for early singular observation families. -/
def matrixMinimum (v : ι → H) (b : ι → ℝ) : H :=
  Fintype.linearCombination ℝ v ((gramMatrix v)⁻¹.mulVec b)

theorem matrixMinimum_eq_minimumVector {v : ι → H} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) : matrixMinimum v b = minimumVector hv b := by
  rw [matrixMinimum, gramMatrix_inverseSource hv]
  rfl

/-- Coordinatewise convergence of the finite rows preserves every signed Gram entry. -/
theorem gramMatrix_tendsto (v : α → ι → H) (w : ι → H)
    (hv : ∀ i, Tendsto (fun t => v t i) l (𝓝 (w i))) :
    Tendsto (fun t => gramMatrix (v t)) l (𝓝 (gramMatrix w)) := by
  apply tendsto_pi_nhds.2
  intro i
  apply tendsto_pi_nhds.2
  intro j
  exact (hv i).inner (hv j)

/-- Positivity of the limiting actual Gram supplies continuity of its inverse. -/
theorem inverseGram_tendsto (v : α → ι → H) {w : ι → H}
    (hw : LinearIndependent ℝ w)
    (hv : ∀ i, Tendsto (fun t => v t i) l (𝓝 (w i))) :
    Tendsto (fun t => (gramMatrix (v t))⁻¹) l (𝓝 ((gramMatrix w)⁻¹)) := by
  have hscalar : ContinuousAt Ring.inverse (gramMatrix w).det := by
    simpa only [Ring.inverse_eq_inv'] using
      (ContinuousInv₀.continuousAt_inv₀ (ne_of_gt (gramMatrix_det_pos hw)))
  exact Filter.Tendsto.comp (continuousAt_matrix_inv (gramMatrix w) hscalar)
    (gramMatrix_tendsto v w hv)

/-- Moving sources converge through the full actual inverse matrix, including
when early approximating Grams happen to be singular. -/
theorem matrixSource_tendsto (v : α → ι → H) {w : ι → H}
    (hw : LinearIndependent ℝ w)
    (hv : ∀ i, Tendsto (fun t => v t i) l (𝓝 (w i)))
    (b : α → ι → ℝ) (c : ι → ℝ)
    (hb : ∀ i, Tendsto (fun t => b t i) l (𝓝 (c i))) :
    Tendsto (fun t => (gramMatrix (v t))⁻¹.mulVec (b t)) l
      (𝓝 (inverseSource hw c)) := by
  have hi := inverseGram_tendsto v hw hv
  rw [← gramMatrix_inverseSource hw c]
  apply tendsto_pi_nhds.2
  intro i
  change Tendsto (fun t => ∑ j, (gramMatrix (v t))⁻¹ i j * b t j) l
    (𝓝 (∑ j, (gramMatrix w)⁻¹ i j * c j))
  exact tendsto_finsetSum Finset.univ (fun j _ =>
    (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hi i) j).mul (hb j))

/-- The represented correction converges strongly while its rows and source move. -/
theorem matrixMinimum_tendsto (v : α → ι → H) {w : ι → H}
    (hw : LinearIndependent ℝ w)
    (hv : ∀ i, Tendsto (fun t => v t i) l (𝓝 (w i)))
    (b : α → ι → ℝ) (c : ι → ℝ)
    (hb : ∀ i, Tendsto (fun t => b t i) l (𝓝 (c i))) :
    Tendsto (fun t => matrixMinimum (v t) (b t)) l (𝓝 (minimumVector hw c)) := by
  have hc := matrixSource_tendsto v hw hv b c hb
  change Tendsto (fun t => ∑ i,
      ((gramMatrix (v t))⁻¹.mulVec (b t)) i • v t i) l
    (𝓝 (∑ i, inverseSource hw c i • w i))
  exact tendsto_finsetSum Finset.univ (fun i _ =>
    (tendsto_pi_nhds.mp hc i).smul (hv i))

/-- The entire signed quadratic value converges; no diagonal terms are isolated. -/
theorem matrixCapacity_tendsto (v : α → ι → H) {w : ι → H}
    (hw : LinearIndependent ℝ w)
    (hv : ∀ i, Tendsto (fun t => v t i) l (𝓝 (w i)))
    (b : α → ι → ℝ) (c : ι → ℝ)
    (hb : ∀ i, Tendsto (fun t => b t i) l (𝓝 (c i))) :
    Tendsto (fun t => ∑ i,
      ((gramMatrix (v t))⁻¹.mulVec (b t)) i * b t i) l (𝓝 (capacity hw c)) := by
  have hc := matrixSource_tendsto v hw hv b c hb
  change Tendsto (fun t => ∑ i,
      ((gramMatrix (v t))⁻¹.mulVec (b t)) i * b t i) l
    (𝓝 (∑ i, inverseSource hw c i * c i))
  exact tendsto_finsetSum Finset.univ (fun i _ =>
    (tendsto_pi_nhds.mp hc i).mul (hb i))

/-- Continuity of the existing minimum-vector construction for varying rows. -/
theorem minimumVector_tendsto (v : α → ι → H) (hv' : ∀ t, LinearIndependent ℝ (v t))
    {w : ι → H} (hw : LinearIndependent ℝ w)
    (hv : ∀ i, Tendsto (fun t => v t i) l (𝓝 (w i)))
    (b : α → ι → ℝ) (c : ι → ℝ)
    (hb : ∀ i, Tendsto (fun t => b t i) l (𝓝 (c i))) :
    Tendsto (fun t => minimumVector (hv' t) (b t)) l (𝓝 (minimumVector hw c)) := by
  have h := matrixMinimum_tendsto v hw hv b c hb
  have he : (fun t => matrixMinimum (v t) (b t)) =
      (fun t => minimumVector (hv' t) (b t)) := by
    funext t
    exact matrixMinimum_eq_minimumVector (hv' t) (b t)
  rwa [he] at h

theorem capacity_tendsto (v : α → ι → H) (hv' : ∀ t, LinearIndependent ℝ (v t))
    {w : ι → H} (hw : LinearIndependent ℝ w)
    (hv : ∀ i, Tendsto (fun t => v t i) l (𝓝 (w i)))
    (b : α → ι → ℝ) (c : ι → ℝ)
    (hb : ∀ i, Tendsto (fun t => b t i) l (𝓝 (c i))) :
    Tendsto (fun t => capacity (hv' t) (b t)) l (𝓝 (capacity hw c)) := by
  have h := matrixCapacity_tendsto v hw hv b c hb
  have he : (fun t => ∑ i, ((gramMatrix (v t))⁻¹.mulVec (b t)) i * b t i) =
      (fun t => capacity (hv' t) (b t)) := by
    funext t
    rw [gramMatrix_inverseSource (hv' t)]
    rfl
  rwa [he] at h

end RiemannResearch.Analysis.FiniteGramContinuity
