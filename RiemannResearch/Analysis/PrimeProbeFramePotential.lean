import RiemannResearch.Analysis.PrimeProbeDualGram
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Exact frame potential and the complete off-diagonal Gram defect

The zero-pair consumer uses prime-phase features from PrimeProbeDualGram.
Source: Datta--Howard--Cochran, Geometry of the Welch Bounds,
https://arxiv.org/abs/0909.0206, for the frame-potential viewpoint.
The exact residual equality below precedes its lower bound.
-/
noncomputable section
open scoped BigOperators ComplexConjugate ComplexOrder
namespace RiemannResearch.Analysis.PrimeProbeDualGram
open ZeroOrdinate MontgomeryPoisson MontgomeryFormFactor
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

def diagonalDefect (A : Matrix κ ι ℂ) : Matrix κ κ ℂ :=
  coordinateGram A - Matrix.diagonal (fun p => coordinateGram A p p)

/-- Parseval on the sample side equals diagonal energy plus the entire
nonnegative off-diagonal coordinate error. No entrywise majorant is used. -/
theorem frame_potential_exact (A : Matrix κ ι ℂ) :
    (∑ i, ∑ j, ‖sampleGram A i j‖ ^ 2) =
      (∑ p, ‖coordinateGram A p p‖ ^ 2) +
        ∑ p, ∑ q, ‖diagonalDefect A p q‖ ^ 2 := by
  classical
  have hG : (coordinateGram A).IsHermitian :=
    (Matrix.posSemidef_self_mul_conjTranspose A).isHermitian
  have hS : (sampleGram A).IsHermitian :=
    (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian
  have he := gram_square_trace_duality A
  rw [hG.trace_mul_self_eq_sum_norm_sq, hS.trace_mul_self_eq_sum_norm_sq] at he
  have heR := congrArg Complex.re he
  simp only [Complex.ofReal_re] at heR
  rw [← heR]
  have entry (p q : κ) :
      ‖coordinateGram A p q‖ ^ 2 =
        (if p = q then ‖coordinateGram A p p‖ ^ 2 else 0) +
          ‖diagonalDefect A p q‖ ^ 2 := by
    by_cases hpq : p = q
    · subst q
      simp [diagonalDefect]
    · simp [diagonalDefect, hpq]
  calc
    _ = ∑ p, ∑ q, ((if p = q then ‖coordinateGram A p p‖ ^ 2 else 0) +
          ‖diagonalDefect A p q‖ ^ 2) := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      exact entry p q
    _ = _ := by simp [Finset.sum_add_distrib]

omit [DecidableEq κ] in
theorem frame_potential_lower (A : Matrix κ ι ℂ) :
    (∑ p, ‖coordinateGram A p p‖ ^ 2) ≤
      ∑ i, ∑ j, ‖sampleGram A i j‖ ^ 2 := by
  classical
  rw [frame_potential_exact]
  exact le_add_of_nonneg_right (by positivity)

omit [Fintype κ] [DecidableEq κ] in
theorem coordinateGram_primeFeature_diagonal
    (t : ι → ℝ) (q b : κ → ℝ) (p : κ) :
    coordinateGram (primeFeature t q b) p p =
      ((Fintype.card ι : ℝ) * b p ^ 2 : ℝ) := by
  simp only [coordinateGram, Matrix.mul_apply, Matrix.conjTranspose_apply,
    primeFeature, star_mul, Complex.star_def, Complex.conj_ofReal]
  have entry (i : ι) :
      ((b p : ℂ) * phase (q p) (t i)) *
        (conj (phase (q p) (t i)) * (b p : ℂ)) = (b p : ℂ)^2 := by
    rw [show ((b p : ℂ) * phase (q p) (t i)) *
        (conj (phase (q p) (t i)) * (b p : ℂ)) =
        (b p : ℂ)^2 * (phase (q p) (t i) * conj (phase (q p) (t i))) by ring,
      Complex.mul_conj, Complex.normSq_eq_norm_sq, phase_norm]
    simp
  simp_rw [entry]
  simp

/-- Weighted phase frame potential, retaining the complete Gram defect.
The sample type may be actual zero copies, including multiplicities. -/
theorem phase_pair_energy_exact (t : ι → ℝ) (q b : κ → ℝ) :
    (∑ i, ∑ j, ‖probeKernel q (fun p => b p ^ 2) (t j - t i)‖ ^ 2) =
      (Fintype.card ι : ℝ)^2 * (∑ p, b p ^ 4) +
        ∑ p, ∑ r, ‖diagonalDefect (primeFeature t q b) p r‖ ^ 2 := by
  have h := frame_potential_exact (primeFeature t q b)
  simp only [sampleGram_primeFeature, coordinateGram_primeFeature_diagonal,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow] at h
  convert h using 1
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  ring

omit [DecidableEq κ] in
theorem phase_pair_energy_lower (t : ι → ℝ) (q b : κ → ℝ) :
    (Fintype.card ι : ℝ)^2 * (∑ p, b p ^ 4) ≤
      ∑ i, ∑ j, ‖probeKernel q (fun p => b p ^ 2) (t j - t i)‖ ^ 2 := by
  classical
  rw [phase_pair_energy_exact]
  exact le_add_of_nonneg_right (by positivity)
end RiemannResearch.Analysis.PrimeProbeDualGram
