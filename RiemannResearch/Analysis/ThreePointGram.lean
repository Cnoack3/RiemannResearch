import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
open scoped BigOperators ComplexConjugate ComplexOrder
open Matrix
/-!
# Three-point Hermitian Gram geometry

Source: user request to compare three primes, using the standard three-by-three
Hermitian determinant and Schur complement identities. The prime-phase
consumer keeps the phase of the complete cycle, rather than only its moduli.
-/
noncomputable section
namespace RiemannResearch.Analysis.ThreePointGram
def correlationMatrix (a b c : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, a, b; star a, 1, c; star b, star c, 1]
theorem determinant_real (a b c : ℂ) :
    (correlationMatrix a b c).det.re =
      1 - Complex.normSq a - Complex.normSq b - Complex.normSq c +
        2 * (a * c * star b).re := by
  simp [correlationMatrix, Matrix.det_fin_three, Complex.mul_re,
    Complex.mul_im, Complex.normSq_apply]
  ring
theorem determinant_imaginary (a b c : ℂ) :
    (correlationMatrix a b c).det.im = 0 := by
  simp [correlationMatrix, Matrix.det_fin_three, Complex.mul_re, Complex.mul_im]
  ring
theorem schur_identity (a b c : ℂ) :
    (correlationMatrix a b c).det.re =
      (1 - Complex.normSq a) * (1 - Complex.normSq b) -
        Complex.normSq (c - star a * b) := by
  rw [determinant_real]
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

end RiemannResearch.Analysis.ThreePointGram

namespace RiemannResearch.Analysis.ThreePointGram
theorem determinant_nonneg (a b c : ℂ)
    (h : (correlationMatrix a b c).PosSemidef) :
    0 ≤ (correlationMatrix a b c).det.re := by
  exact (Complex.nonneg_iff.mp h.det_nonneg).1
theorem schur_disk (a b c : ℂ)
    (h : (correlationMatrix a b c).PosSemidef) :
    Complex.normSq (c - star a * b) ≤
      (1 - Complex.normSq a) * (1 - Complex.normSq b) := by
  have hh := determinant_nonneg a b c h
  rw [schur_identity] at hh
  linarith
end RiemannResearch.Analysis.ThreePointGram
