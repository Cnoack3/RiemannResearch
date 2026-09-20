import RiemannResearch.Analysis.ReciprocalMellinSymmetry
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring

/-!
# Reflection and conjugation of finite complex kernels

Source: user-provided reciprocal Mellin DPP construction (2026-09-20).
The determinant identities below encode symmetry of finite correlation
functions. They do not identify the random particles with zeta zeros.
For DPP terminology see Hough--Krishnapur--Peres--Virag,
https://arxiv.org/abs/math/0503110.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.ReflectedKernel

/-- Kernel of a finite family of complex feature functions. -/
def featureKernel {ι X : Type*} [Fintype ι] (φ : ι → X → ℂ) (x y : X) : ℂ :=
  ∑ i, φ i x * star (φ i y)

/-- The sum of a kernel and its image under an involution. -/
def completion {X : Type*} (r : X → X) (K : X → X → ℂ) (x y : X) : ℂ :=
  K x y + K (r x) (r y)

theorem featureKernel_hermitian {ι X : Type*} [Fintype ι]
    (φ : ι → X → ℂ) (x y : X) :
    featureKernel φ y x = star (featureKernel φ x y) := by
  simp only [featureKernel, star_sum, star_mul, star_star]

theorem featureKernel_reflection {ι X : Type*} [Fintype ι]
    (φ : ι → X → ℂ) (r : X → X)
    (hφ : ∀ i x, φ i (r x) = star (φ i x)) (x y : X) :
    featureKernel φ (r x) (r y) = star (featureKernel φ x y) := by
  simp only [featureKernel, hφ, star_sum, star_mul, star_star]
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_comm _ _

theorem completion_invariant {X : Type*} (r : X → X)
    (hr : Function.Involutive r) (K : X → X → ℂ) (x y : X) :
    completion r K (r x) (r y) = completion r K x y := by
  change K (r x) (r y) + K (r (r x)) (r (r y)) =
    K x y + K (r x) (r y)
  rw [hr x, hr y]
  exact add_comm (K (r x) (r y)) (K x y)

theorem completion_eq_twice_re {X : Type*} (r : X → X)
    (K : X → X → ℂ)
    (hK : ∀ x y, K (r x) (r y) = star (K x y)) (x y : X) :
    completion r K x y = (2 * (K x y).re : ℝ) := by
  rw [completion, hK]
  apply Complex.ext <;> simp <;> ring

theorem completion_real {X : Type*} (r : X → X)
    (K : X → X → ℂ)
    (hK : ∀ x y, K (r x) (r y) = star (K x y)) (x y : X) :
    star (completion r K x y) = completion r K x y := by
  rw [completion_eq_twice_re r K hK]
  simp

/-- Reflection conjugates a Hermitian matrix into its transpose, preserving
every finite correlation determinant. -/
theorem correlation_reflection {X ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : X → X) (K : X → X → ℂ)
    (hR : ∀ x y, K (r x) (r y) = star (K x y))
    (hH : ∀ x y, K y x = star (K x y)) (a : ι → X) :
    Matrix.det (Matrix.of (fun i j => K (r (a i)) (r (a j)))) =
      Matrix.det (Matrix.of (fun i j => K (a i) (a j))) := by
  have hm : Matrix.of (fun i j => K (r (a i)) (r (a j))) =
      (Matrix.of (fun i j => K (a i) (a j))).transpose := by
    apply Matrix.ext
    intro i j
    exact (hR _ _).trans (hH _ _).symm
  rw [hm]
  exact Matrix.det_transpose _

theorem feature_correlation_reflection {X ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (φ : ι → X → ℂ) (r : X → X)
    (hφ : ∀ i x, φ i (r x) = star (φ i x)) (a : κ → X) :
    Matrix.det (Matrix.of (fun i j => featureKernel φ (r (a i)) (r (a j)))) =
      Matrix.det (Matrix.of (fun i j => featureKernel φ (a i) (a j))) :=
  correlation_reflection r (featureKernel φ)
    (featureKernel_reflection φ r hφ) (featureKernel_hermitian φ) a


/-- Mellin boundary features obtained from real physical functions. -/
def realMellinFeatures {ι : Type*} (f : ι → ℝ → ℝ) (i : ι) (t : ℝ) : ℂ :=
  ReciprocalMellin.transform (fun x => (f i x : ℂ)) (ReciprocalMellin.criticalPoint t)

theorem realMellinFeatures_neg {ι : Type*} (f : ι → ℝ → ℝ) (i : ι) (t : ℝ) :
    realMellinFeatures f i (-t) = star (realMellinFeatures f i t) := by
  exact ReciprocalMellin.transform_critical_neg_of_real
    (fun x => (f i x : ℂ)) (by intro x; simp) t

theorem realMellinKernel_reflection {ι : Type*} [Fintype ι]
    (f : ι → ℝ → ℝ) (t u : ℝ) :
    featureKernel (realMellinFeatures f) (-t) (-u) =
      star (featureKernel (realMellinFeatures f) t u) :=
  featureKernel_reflection _ Neg.neg (realMellinFeatures_neg f) t u

theorem realMellinKernel_completion {ι : Type*} [Fintype ι]
    (f : ι → ℝ → ℝ) (t u : ℝ) :
    completion Neg.neg (featureKernel (realMellinFeatures f)) t u =
      (2 * (featureKernel (realMellinFeatures f) t u).re : ℝ) :=
  completion_eq_twice_re Neg.neg _ (realMellinKernel_reflection f) t u

theorem realMellinKernel_correlation_reflection {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (f : ι → ℝ → ℝ) (a : κ → ℝ) :
    Matrix.det (Matrix.of (fun i j => featureKernel (realMellinFeatures f) (-a i) (-a j))) =
      Matrix.det (Matrix.of (fun i j => featureKernel (realMellinFeatures f) (a i) (a j))) :=
  feature_correlation_reflection _ Neg.neg (realMellinFeatures_neg f) a

end RiemannResearch.Analysis.ReflectedKernel
