import RiemannResearch.Analysis.ActualZeroOrdinate
import RiemannResearch.Analysis.ProjectionDPPKernel
import RiemannResearch.Probability.DeterminantalExistence
import RiemannResearch.Probability.DeterminantalEntry
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Projection DPP on actual zero labels from real Fourier features

Source: Lyons, Determinantal probability measures, https://arxiv.org/abs/math/0204325,
for the discrete projection-DPP construction. FMZ prime-log frequencies are
a specialization of the arbitrary frequencies allowed here.
The law selects labelled copies of actual zeros. It does not assert that
the unthinned deterministic zeros have a determinantal distribution.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace RiemannResearch.Probability.DPP.ZeroOrdinateProjection
open RiemannResearch.Analysis
open ActualZeroOrdinate ProjectionDPP
abbrev Space (T : ℝ) := EuclideanSpace ℝ (Copies T)

def feature {κ : Type*} (T : ℝ) (q : κ → ℝ) (k : κ × Bool) : Space T :=
  WithLp.toLp 2 (fun i : Copies T =>
    if k.2 then Real.sin (q k.1 * i.1.1.im) else Real.cos (q k.1 * i.1.1.im))

def featureSpace {κ : Type*} (T : ℝ) (q : κ → ℝ) : Submodule ℝ (Space T) :=
  Submodule.span ℝ (Set.range (feature T q))

open Classical in
def coordinate (T : ℝ) : Copies T → Space T := EuclideanSpace.basisFun (Copies T) ℝ

open Classical in
theorem coordinate_inner (T : ℝ) (i j : Copies T) :
    inner ℝ (coordinate T i) (coordinate T j) = if i = j then 1 else 0 := by
  classical
  change inner ℝ ((EuclideanSpace.basisFun (Copies T) ℝ) i)
    ((EuclideanSpace.basisFun (Copies T) ℝ) j) = _
  rw [EuclideanSpace.basisFun_inner, EuclideanSpace.basisFun_apply]
  simp

def zeroKernel {κ : Type*} (T : ℝ) (q : κ → ℝ) : Copies T → Copies T → ℝ :=
  kernel (featureSpace T q) (coordinate T)

open Classical in
def law {κ : Type*} (T : ℝ) (q : κ → ℝ) : Measure (Copies T → Bool) :=
  contractionDPP (zeroKernel T q)
    (fun I => principal_posSemidef (featureSpace T q) (coordinate T) (fun i : I => i.1))
    (fun I => by
      have h := identity_sub_principal_posSemidef (featureSpace T q) (coordinate T)
        (fun i : I => i.1) (by intro i j; simp [coordinate_inner])
      convert h using 1
      ext i j
      simp [Matrix.sub_apply, Matrix.one_apply, zeroKernel, kernel])

instance law_probability {κ : Type*} (T : ℝ) (q : κ → ℝ) :
    IsProbabilityMeasure (law T q) := by
  unfold law
  exact contractionDPP_probability _ _ _

theorem law_isDPP {κ : Type*} (T : ℝ) (q : κ → ℝ) :
    IsDPP (law T q) (fun x => {i | x i = true}) (zeroKernel T q) :=
  contractionDPP_isDPP _ _ _

theorem law_two_point {κ : Type*} (T : ℝ) (q : κ → ℝ)
    {i j : Copies T} (hij : i ≠ j) :
    (law T q).real {x | x i = true ∧ x j = true} =
      zeroKernel T q i i * zeroKernel T q j j - (zeroKernel T q i j)^2 := by
  have h := (law_isDPP T q).two_point hij
  have hs : zeroKernel T q j i = zeroKernel T q i j :=
    kernel_symmetric _ _ j i
  simpa only [Set.mem_ofPred_eq, hs, pow_two] using h

end RiemannResearch.Probability.DPP.ZeroOrdinateProjection
