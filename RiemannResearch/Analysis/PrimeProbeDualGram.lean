import RiemannResearch.Analysis.MontgomeryPrimeProbe
import RiemannResearch.Probability.ContinuousProjectionCompression
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Ring

/-!
# Coordinate/sample duality for prime-phase Gram matrices

Source: user-provided V_vector_space_RH.pdf, Sections 3 and 5, for the
covariance interpretation; Sylvester's determinant identity for the finite
duality; Hough--Krishnapur--Peres--Virag, arXiv:math/0503110, for the DPP
spectral-count interpretation when the Gram matrix is a positive contraction.

The coordinate Gram and sample Gram have identical determinant generating
functions, traces and square traces. For prime-phase features the sample Gram
is the explicit probe at the difference of ordinates. Thus the covariance
purity is exactly a weighted pair statistic, with diagonal and multiplicity
terms retained. The sample index may be actual zero copies, but no zero
asymptotic or DPP identification of the deterministic zeros follows.
-/

noncomputable section
open scoped BigOperators ComplexConjugate ComplexOrder
namespace RiemannResearch.Analysis.PrimeProbeDualGram
open RiemannResearch.Analysis.MontgomeryFormFactor
open RiemannResearch.Analysis.ZeroOrdinate
open RiemannResearch.Analysis.MontgomeryPoisson
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def coordinateGram (A : Matrix κ ι ℂ) : Matrix κ κ ℂ :=
  A * A.conjTranspose

def sampleGram (A : Matrix κ ι ℂ) : Matrix ι ι ℂ :=
  A.conjTranspose * A

theorem gram_trace_duality (A : Matrix κ ι ℂ) :
    (coordinateGram A).trace = (sampleGram A).trace :=
  Matrix.trace_mul_comm A A.conjTranspose

theorem gram_square_trace_duality (A : Matrix κ ι ℂ) :
    (coordinateGram A * coordinateGram A).trace =
      (sampleGram A * sampleGram A).trace := by
  simpa only [coordinateGram, sampleGram, Matrix.mul_assoc] using
    Matrix.trace_mul_comm A (A.conjTranspose * (A * A.conjTranspose))

theorem gram_determinant_duality [DecidableEq ι] [DecidableEq κ] (A : Matrix κ ι ℂ) (z : ℂ) :
    (1 + z • coordinateGram A).det = (1 + z • sampleGram A).det := by
  simpa only [coordinateGram, sampleGram, Matrix.smul_mul, Matrix.mul_smul] using
    Matrix.det_one_add_mul_comm (z • A) A.conjTranspose

def primeFeature (t : ι → ℝ) (q b : κ → ℝ) : Matrix κ ι ℂ :=
  fun p i => (b p : ℂ) * phase (q p) (t i)

theorem sampleGram_primeFeature (t : ι → ℝ) (q b : κ → ℝ) (i j : ι) :
    sampleGram (primeFeature t q b) i j =
      probeKernel q (fun p => b p ^ 2) (t j - t i) := by
  simp only [sampleGram, Matrix.mul_apply, Matrix.conjTranspose_apply,
    primeFeature, star_mul, Complex.star_def, Complex.conj_ofReal, probeKernel]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← phase_mul_conj (q p) (t j) (t i)]
  push_cast
  ring

theorem primeFeature_square_trace (t : ι → ℝ) (q b : κ → ℝ) :
    (coordinateGram (primeFeature t q b) *
      coordinateGram (primeFeature t q b)).trace =
      ((∑ i, ∑ j, ‖probeKernel q (fun p => b p ^ 2) (t j - t i)‖ ^ 2 : ℝ) : ℂ) := by
  rw [gram_square_trace_duality]
  classical
  have h : (sampleGram (primeFeature t q b)).IsHermitian :=
    (Matrix.posSemidef_conjTranspose_mul_self (primeFeature t q b)).isHermitian
  rw [h.trace_mul_self_eq_sum_norm_sq]
  simp_rw [sampleGram_primeFeature]

end RiemannResearch.Analysis.PrimeProbeDualGram
