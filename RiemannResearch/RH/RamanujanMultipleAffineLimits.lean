import RiemannResearch.RH.RamanujanMultipleCapacityLimits
import RiemannResearch.RH.RamanujanMultipleConstraints
import RiemannResearch.RH.RamanujanCoefficientLimits
import RiemannResearch.Analysis.FiniteGramContinuity
import RiemannResearch.Analysis.MultipleAffineObservationProjection
import RiemannResearch.Analysis.FiniteGramMultipleConstraint
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Closed affine multiple-coordinate optimizers and moving target limits

Source: user-requested fourth Ramanujan dual continuation, 23 October 2026.
The limiting source Gram constructs the unique optimizer in the entire
closed legal space for any finite vector of prescribed original coefficients.
Finite packet optimizers converge strongly for arbitrary moving target
vectors along cofinal filters. Only the limiting source Gram must be
invertible; early stages can fail to contain the chosen conductors.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.RamanujanMultipleAffineLimits
open Pareto Pareto.CoefficientStabilization RamanujanCanonicalOptimizer
open RamanujanCoefficientConstraints RamanujanMultipleCapacityLimits
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteHilbertConstraints
open RiemannResearch.Analysis.FiniteGramCapacity
open RiemannResearch.Analysis.FiniteGramContinuity
open RiemannResearch.Analysis.MultipleAffineObservationProjection

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def finiteDefect (n : ℕ) (e : κ ↪ ℕ) (t : κ → ℝ) (j : κ) : ℝ :=
  t j - packetMultipleCoefficient n (e j + 2)

def limitDefect (e : κ ↪ ℕ) (t : κ → ℝ) (j : κ) : ℝ :=
  t j - limitCoefficient (e j + 2)

/-- The matrix formula is totalized for early stages; once the conductors
enter the stage it is precisely the previously constructed legal optimizer. -/
def affineFiniteCandidate (n : ℕ) (e : κ ↪ ℕ) (t : κ → ℝ) : ThresholdHilbert :=
  packetCandidate n + matrixMinimum (finiteRows n e) (finiteDefect n e t)

def affineLimitCandidate (e : κ ↪ ℕ) (t : κ → ℝ) : ThresholdHilbert :=
  limitProjection + minimumVector (limitRows_independent e) (limitDefect e t)

def limitCost (e : κ ↪ ℕ) (t : κ → ℝ) : ℝ :=
  capacity (limitRows_independent e) (limitDefect e t)

theorem affineFiniteCandidate_eq_stage (n : ℕ) (e : κ ↪ ℕ) (hn : ∀ j, e j < n)
    (t : κ → ℝ) : affineFiniteCandidate n e t =
      RamanujanMultipleConstraints.constrainedCandidate n (stageEmbedding n e hn) t := by
  rw [affineFiniteCandidate, finiteRows_eq_stageRows n e hn,
    matrixMinimum_eq_minimumVector (RamanujanMultipleConstraints.rows_independent n (stageEmbedding n e hn))]
  have h := RiemannResearch.Analysis.FiniteGramMultipleConstraint.coefficients_synthesis
    (finitePacket_independent n)
    (RamanujanMultipleConstraints.sources n (stageEmbedding n e hn))
    (RamanujanMultipleConstraints.rows_independent n (stageEmbedding n e hn)) hilbertOne t
  rw [RamanujanMultipleConstraints.mismatch_eq] at h
  change RamanujanMultipleConstraints.constrainedCandidate n (stageEmbedding n e hn) t =
    packetCandidate n + minimumVector
      (RamanujanMultipleConstraints.rows_independent n (stageEmbedding n e hn))
      (RamanujanMultipleConstraints.defect n (stageEmbedding n e hn) t) at h
  exact h.symm

theorem limitMismatch_eq (e : κ ↪ ℕ) (t : κ → ℝ) :
    affineMismatch closedSpace (limitRows e) hilbertOne t = limitDefect e t := by
  funext j
  change t j - inner ℝ (coordinateLimitRepresenter (e j + 2)) limitProjection =
    t j - coefficientCLM (e j + 2) limitProjection
  rw [coordinateLimitRepresenter_inner (e j + 2) limitProjection
    (show limitProjection ∈ closedSpace from closedSpace.starProjection_apply_mem hilbertOne)]

theorem affineLimitCandidate_eq (e : κ ↪ ℕ) (t : κ → ℝ) :
    affineLimitCandidate e t = affineCandidate closedSpace (limitRows_independent e) hilbertOne t := by
  rw [affineCandidate, limitMismatch_eq]
  rfl

theorem affineLimitCandidate_mem (e : κ ↪ ℕ) (t : κ → ℝ) :
    affineLimitCandidate e t ∈ closedSpace := by
  rw [affineLimitCandidate_eq]
  exact affineCandidate_mem closedSpace (limitRows_independent e) (limitRows_mem e) hilbertOne t

theorem affineLimitCandidate_coordinates (e : κ ↪ ℕ) (t : κ → ℝ) (j : κ) :
    coefficientCLM (e j + 2) (affineLimitCandidate e t) = t j := by
  have h := affineCandidate_observation closedSpace (limitRows_independent e) hilbertOne t j
  rw [← affineLimitCandidate_eq] at h
  change inner ℝ (coordinateLimitRepresenter (e j + 2)) (affineLimitCandidate e t) = t j at h
  rwa [coordinateLimitRepresenter_inner _ _ (affineLimitCandidate_mem e t)] at h

/-- The limiting error contains the complete canonical residual and the full
inverse source-Gram penalty, including every mixed conductor contribution. -/
theorem affineLimitCandidate_error (e : κ ↪ ℕ) (t : κ → ℝ) :
    ‖hilbertOne - affineLimitCandidate e t‖ ^ 2 = limitEnergy + limitCost e t := by
  have h := affineCandidate_energy closedSpace (limitRows_independent e)
    (limitRows_mem e) hilbertOne t
  rw [limitMismatch_eq, ← affineLimitCandidate_eq] at h
  exact h

theorem limitCost_inverseGram (e : κ ↪ ℕ) (t : κ → ℝ) :
    limitCost e t = dotProduct (limitDefect e t) ((limitGram e)⁻¹.mulVec (limitDefect e t)) := by
  rw [limitGram, gramMatrix_inverseSource (limitRows_independent e)]
  unfold limitCost capacity dotProduct
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem affineLimitCandidate_completion (e : κ ↪ ℕ) (t : κ → ℝ)
    (y : ThresholdHilbert) (hy : y ∈ closedSpace)
    (hyt : ∀ j, coefficientCLM (e j + 2) y = t j) :
    ‖hilbertOne - y‖ ^ 2 = limitEnergy + limitCost e t + ‖y - affineLimitCandidate e t‖ ^ 2 := by
  have hobs : ∀ j, inner ℝ (limitRows e j) y = t j := by
    intro j
    exact (coordinateLimitRepresenter_inner (e j + 2) y hy).trans (hyt j)
  have h := affineCandidate_completion closedSpace (limitRows_independent e) hilbertOne t y hy hobs
  rw [limitMismatch_eq, ← affineLimitCandidate_eq] at h
  exact h

theorem affineLimitCandidate_optimal_iff (e : κ ↪ ℕ) (t : κ → ℝ)
    (y : ThresholdHilbert) (hy : y ∈ closedSpace)
    (hyt : ∀ j, coefficientCLM (e j + 2) y = t j) :
    ‖hilbertOne - y‖ ^ 2 = limitEnergy + limitCost e t ↔ y = affineLimitCandidate e t := by
  constructor
  · intro he
    have hc := affineLimitCandidate_completion e t y hy hyt
    have hz : ‖y - affineLimitCandidate e t‖ ^ 2 = 0 := by linarith
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))
  · rintro rfl
    exact affineLimitCandidate_error e t

/-- All prescribed values may move independently along any cofinal filter. -/
theorem affineFiniteCandidate_tendsto {α : Type*} {l : Filter α}
    (N : α → ℕ) (hN : Tendsto N l atTop) (e : κ ↪ ℕ)
    (t : α → κ → ℝ) (t₀ : κ → ℝ)
    (ht : ∀ j, Tendsto (fun i => t i j) l (𝓝 (t₀ j))) :
    Tendsto (fun i => affineFiniteCandidate (N i) e (t i)) l (𝓝 (affineLimitCandidate e t₀)) := by
  have hp : Tendsto (fun i => packetCandidate (N i)) l (𝓝 limitProjection) := by
    simpa only [packetCandidate_eq_projection, Function.comp_def] using projection_tendsto.comp hN
  have hr : ∀ j, Tendsto (fun i => finiteRows (N i) e j) l (𝓝 (limitRows e j)) := by
    intro j
    exact (finiteRows_tendsto e j).comp hN
  have hb : ∀ j, Tendsto (fun i => finiteDefect (N i) e (t i) j) l (𝓝 (limitDefect e t₀ j)) := by
    intro j
    exact (ht j).sub ((packetMultipleCoefficient_tendsto (e j + 2) (by omega)).comp hN)
  have hc := matrixMinimum_tendsto (fun i => finiteRows (N i) e)
    (limitRows_independent e) hr (fun i => finiteDefect (N i) e (t i)) (limitDefect e t₀) hb
  exact hp.add hc

theorem affineFiniteCandidate_error_tendsto {α : Type*} {l : Filter α}
    (N : α → ℕ) (hN : Tendsto N l atTop) (e : κ ↪ ℕ)
    (t : α → κ → ℝ) (t₀ : κ → ℝ)
    (ht : ∀ j, Tendsto (fun i => t i j) l (𝓝 (t₀ j))) :
    Tendsto (fun i => ‖hilbertOne - affineFiniteCandidate (N i) e (t i)‖ ^ 2) l
      (𝓝 (limitEnergy + limitCost e t₀)) := by
  have h := ((tendsto_const_nhds (x := hilbertOne)).sub (affineFiniteCandidate_tendsto N hN e t t₀ ht)).norm.pow 2
  rwa [affineLimitCandidate_error] at h

end RiemannResearch.RH.RamanujanMultipleAffineLimits
