import RiemannResearch.Analysis.ComplexKernelPairCorrelation

/-!
# Pair-density convergence from kernel convergence

Source: user-provided Montgomery comparison, 2026-09-20. The theorem is
continuity of the exact two-point expression at nonzero limiting diagonal
entries. It does not assert that any particular kernel limit exists.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.Analysis.ComplexKernel

variable {X I : Type*}

theorem normalized_pairDensity_tendsto
    (K : I → X → X → ℂ) (A : X → X → ℂ) (l : Filter I)
    (hK : ∀ x y, Tendsto (fun i => K i x y) l (𝓝 (A x y)))
    (x y : X) (hx : (A x x).re ≠ 0) (hy : (A y y).re ≠ 0) :
    Tendsto (fun i => pairDensity (K i) x y /
      ((K i x x).re * (K i y y).re)) l
      (𝓝 (1 - ‖A x y‖ ^ 2 / ((A x x).re * (A y y).re))) := by
  have hd := ((Complex.continuous_re.tendsto (A x x)).comp (hK x x)).mul
    ((Complex.continuous_re.tendsto (A y y)).comp (hK y y))
  have hn := (hK x y).norm.pow 2
  have ht := (hd.sub hn).div hd (mul_ne_zero hx hy)
  have he :
      ((A x x).re * (A y y).re - ‖A x y‖ ^ 2) /
        ((A x x).re * (A y y).re) =
      1 - ‖A x y‖ ^ 2 / ((A x x).re * (A y y).re) := by
    field_simp
  change Tendsto (fun i =>
      ((K i x x).re * (K i y y).re - ‖K i x y‖ ^ 2) /
        ((K i x x).re * (K i y y).re)) l
      (𝓝 (((A x x).re * (A y y).re - ‖A x y‖ ^ 2) /
        ((A x x).re * (A y y).re))) at ht
  rw [he] at ht
  exact ht

end RiemannResearch.Analysis.ComplexKernel
