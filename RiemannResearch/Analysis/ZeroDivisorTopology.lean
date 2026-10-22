import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Coordinate tails and continued zero evaluation

Source: user-provided argument, V_Zeta_Vector_Spaces_Research_2026-09-16.md,
Section 6. These declarations separate established Hilbert topology from the
provider identifying a continued arithmetic Dirichlet function. In particular,
the continued-evaluation formula is an explicit hypothesis below; this module
does not assert that every square-summable coordinate vector has continuation.
-/

noncomputable section

namespace RiemannResearch.Analysis

open Filter Set
open scoped Topology BigOperators

/-- The report's weighted coordinates become ordinary complex `lp` coordinates
after multiplication by their positive coordinate weights. -/
abbrev ComplexCoordinates (ι : Type*) := lp (fun _ : ι => ℂ) 2

section Coordinates
variable {ι : Type*} [DecidableEq ι]

/-- A finite coordinate truncation. -/
noncomputable def coordinateHead (h : ComplexCoordinates ι) (s : Finset ι) :
    ComplexCoordinates ι := ∑ i ∈ s, lp.single 2 i (h i)

/-- The complement of a finite coordinate truncation. -/
noncomputable def coordinateTail (h : ComplexCoordinates ι) (s : Finset ι) :
    ComplexCoordinates ι := h - coordinateHead h s

theorem coordinateHead_tendsto (h : ComplexCoordinates ι) :
    Tendsto (coordinateHead h) atTop (𝓝 h) := by
  exact lp.hasSum_single (by simp) h

theorem coordinateTail_tendsto_zero (h : ComplexCoordinates ι) :
    Tendsto (coordinateTail h) atTop (𝓝 0) := by
  change Tendsto (fun s => h - coordinateHead h s) atTop (𝓝 0)
  simpa only [sub_self] using
    (coordinateHead_tendsto h).const_sub h

/-- The set of all finite coordinate truncations of arbitrary vectors. -/
def finiteCoordinateVectors : Set (ComplexCoordinates ι) :=
  Set.range (fun p : Finset ι × ComplexCoordinates ι => coordinateHead p.2 p.1)

theorem finiteCoordinateVectors_dense : Dense (finiteCoordinateVectors (ι := ι)) := by
  intro x
  apply mem_closure_of_tendsto (coordinateHead_tendsto x)
  exact Filter.Eventually.of_forall (fun s => ⟨(s, x), rfl⟩)

/-- The two classes in Section 6 are simultaneously dense. This statement is
pure Hilbert topology and has no zeta or analytic-continuation hypothesis. -/
theorem finiteCoordinateVectors_and_translate_dense (η : ComplexCoordinates ι) :
    Dense (finiteCoordinateVectors (ι := ι)) ∧
      Dense ((fun x => η + x) '' finiteCoordinateVectors (ι := ι)) := by
  refine ⟨finiteCoordinateVectors_dense, ?_⟩
  intro x
  have ht : Tendsto (fun s => η + coordinateHead (x - η) s) atTop (𝓝 x) := by
    simpa only [add_comm η (x - η), sub_add_cancel] using
      (coordinateHead_tendsto (x - η)).const_add η
  apply mem_closure_of_tendsto ht
  exact Filter.Eventually.of_forall (fun s =>
    ⟨coordinateHead (x - η) s, ⟨(s, x - η), rfl⟩, rfl⟩)

/-- Even the minimal domain consisting of zero and the coordinate tails is
enough to witness the discontinuity. -/
def coordinateTailDomain (η : ComplexCoordinates ι) : Set (ComplexCoordinates ι) :=
  {0} ∪ Set.range (coordinateTail η)

/-- Conditional research reduction: the domain-specific continuation provider
is `htail`. Hilbert convergence of the tails is proved, not assumed. -/
theorem continued_eval_not_continuousWithinAt_zero
    (η : ComplexCoordinates ι) (evaluate : ComplexCoordinates ι → ℂ)
    (H : Finset ι → ℂ) (ρ : ℂ) (hρ : riemannZeta ρ = 0)
    (hzero : evaluate 0 = 1)
    (htail : ∀ s, evaluate (coordinateTail η s) =
      riemannZeta ρ * Complex.exp (-H s)) :
    ¬ ContinuousWithinAt evaluate (coordinateTailDomain η) 0 := by
  intro hc
  have hwithin : Tendsto (coordinateTail η) atTop
      (𝓝[coordinateTailDomain η] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨coordinateTail_tendsto_zero η, ?_⟩
    exact Filter.Eventually.of_forall (fun s => Or.inr ⟨s, rfl⟩)
  have hone : Tendsto (fun s => evaluate (coordinateTail η s)) atTop (𝓝 1) := by
    simpa only [hzero, Function.comp_def] using hc.tendsto.comp hwithin
  have heval : (fun s => evaluate (coordinateTail η s)) = (fun _ => (0 : ℂ)) := by
    funext s
    simp only [htail, hρ, zero_mul]
  have hlimzero : Tendsto (fun s => evaluate (coordinateTail η s)) atTop (𝓝 0) := by
    rw [heval]
    exact tendsto_const_nhds
  exact zero_ne_one (tendsto_nhds_unique hlimzero hone)

end Coordinates

/-- A logarithmic perturbation multiplies its associated function by a
nowhere-zero exponential; no analytic hypothesis is needed for its zero set. -/
theorem mul_cexp_eq_zero_iff (F H : ℂ → ℂ) (z : ℂ) :
    F z * Complex.exp (H z) = 0 ↔ F z = 0 := by
  simp only [mul_eq_zero, Complex.exp_ne_zero, or_false]

/-- In particular, every finite logarithmic perturbation preserves zeta zeros.
The parameter `H` can also be any other complex-valued function. -/
theorem zeta_mul_cexp_eq_zero_iff (H : ℂ → ℂ) (z : ℂ) :
    riemannZeta z * Complex.exp (H z) = 0 ↔ riemannZeta z = 0 := by
  exact mul_cexp_eq_zero_iff riemannZeta H z

/-- Analytic exponential perturbations preserve the full analytic zero order,
including infinite order. This supplies multiplicity preservation. -/
theorem analyticOrderAt_mul_cexp {F H : ℂ → ℂ} {z : ℂ}
    (hF : AnalyticAt ℂ F z) (hH : AnalyticAt ℂ H z) :
    analyticOrderAt (fun w => F w * Complex.exp (H w)) z = analyticOrderAt F z := by
  have hE : AnalyticAt ℂ (fun w => Complex.exp (H w)) z := hH.cexp
  have horder : analyticOrderAt (fun w => Complex.exp (H w)) z = 0 :=
    (hE.analyticOrderAt_eq_zero).2 (Complex.exp_ne_zero (H z))
  change analyticOrderAt (F * (fun w => Complex.exp (H w))) z = _
  rw [analyticOrderAt_mul hF hE, horder, add_zero]

end RiemannResearch.Analysis
