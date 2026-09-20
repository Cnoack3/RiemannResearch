import RiemannResearch.Analysis.ComplexKernelPairCorrelation
import RiemannResearch.RH.IntegerDPPGramDeterminant
import RiemannResearch.Analysis.MellinNormalizedResidue

/-!
# Exact arithmetic Mellin frequency kernel

Source: user-provided Mellin DPP and Montgomery pair-correlation discussion,
2026-09-20. All transforms below are actual Pareto Mellin integrals. The
inverse is that of the full infinite-tail Pareto Gram matrix. The resulting
kernel factorization and normalized pair expression are algebraic facts.

This file does not claim that a continuum DPP has been constructed, a
sine-kernel limit has been proved, or that its random points are zeta zeros.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.MellinFrequency
open CoefficientStabilization
open IntegerDPP
open RiemannResearch.Analysis.ComplexKernel

def criticalPoint (t : ℝ) : ℂ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I

@[simp] theorem criticalPoint_re (t : ℝ) : (criticalPoint t).re = 1 / 2 := by
  simp [criticalPoint]

theorem criticalPoint_ne_zero (t : ℝ) : criticalPoint t ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

theorem criticalPoint_ne_one (t : ℝ) : criticalPoint t ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  simp at this

def zetaEnvelope (t : ℝ) : ℂ := riemannZeta (criticalPoint t) / criticalPoint t

def residueSymbol (i : ℕ) (t : ℝ) : ℂ :=
  1 / ((i + 2 : ℕ) : ℂ) - ((i + 2 : ℕ) : ℂ) ^ (-criticalPoint t)

theorem residueAtom_transform (i : ℕ) (t : ℝ) :
    paretoMellin (residueAtom i) (criticalPoint t) =
      zetaEnvelope t * residueSymbol i t := by
  have h := normalizedResidue_mellin_zeta (i + 2) (by omega)
    (criticalPoint t) (by simp) (criticalPoint_ne_one t)
  change criticalPoint t * paretoMellin (residueAtom i) (criticalPoint t) =
    residueSymbol i t * riemannZeta (criticalPoint t) at h
  apply (mul_left_cancel₀ (criticalPoint_ne_zero t))
  rw [h]
  unfold zetaEnvelope
  field_simp [criticalPoint_ne_zero t]

/-- The exact inverse-Gram expression before inserting the zeta envelope. -/
def core (n : ℕ) (t u : ℝ) : ℂ :=
  ∑ i : Fin n, ∑ j : Fin n,
    residueSymbol i.val t * (((fullGram n)⁻¹ i j : ℝ) : ℂ) *
      star (residueSymbol j.val u)

private theorem fullGram_inverse_symmetric (n : ℕ) (i j : Fin n) :
    (fullGram n)⁻¹ i j = (fullGram n)⁻¹ j i := by
  have hG : (fullGram n).IsSymm := by
    ext i j
    change inner ℝ (residueAtom j.val) (residueAtom i.val) =
      inner ℝ (residueAtom i.val) (residueAtom j.val)
    exact real_inner_comm (residueAtom i.val) (residueAtom j.val)
  have hI : ((fullGram n)⁻¹).transpose = (fullGram n)⁻¹ := hG.inv
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hI
  exact h.symm

theorem core_hermitian (n : ℕ) (t u : ℝ) :
    star (core n u t) = core n t u := by
  unfold core
  simp only [Complex.star_def, map_sum, map_mul,
    Complex.conj_conj, Complex.conj_ofReal]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [fullGram_inverse_symmetric n j i]
  ring

theorem core_diagonal_im_zero (n : ℕ) (t : ℝ) : (core n t t).im = 0 := by
  have h := congrArg Complex.im (core_hermitian n t t)
  simp only [Complex.star_def, Complex.conj_im] at h
  linarith

/-- Relative to dt/(2π), the candidate projection kernel from actual Mellin
features and the actual Pareto Gram inverse. -/
def kernel (n : ℕ) (t u : ℝ) : ℂ :=
  ∑ i : Fin n, ∑ j : Fin n,
    paretoMellin (residueAtom i.val) (criticalPoint t) *
      (((fullGram n)⁻¹ i j : ℝ) : ℂ) *
      star (paretoMellin (residueAtom j.val) (criticalPoint u))

theorem kernel_factorization (n : ℕ) (t u : ℝ) :
    kernel n t u = envelopeKernel zetaEnvelope (core n) t u := by
  simp only [kernel, residueAtom_transform, star_mul]
  unfold envelopeKernel core
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem kernel_eq_envelope (n : ℕ) :
    kernel n = envelopeKernel zetaEnvelope (core n) := by
  funext t u
  exact kernel_factorization n t u

theorem kernel_hermitian (n : ℕ) (t u : ℝ) :
    star (kernel n u t) = kernel n t u := by
  rw [kernel_factorization, kernel_factorization]
  simp only [envelopeKernel, star_mul, star_star, core_hermitian]
  ring

theorem kernel_diagonal_im_zero (n : ℕ) (t : ℝ) : (kernel n t t).im = 0 := by
  have h := congrArg Complex.im (kernel_hermitian n t t)
  simp only [Complex.star_def, Complex.conj_im] at h
  linarith

theorem kernel_row_zero_of_zeta_zero (n : ℕ) {t : ℝ}
    (ht : riemannZeta (criticalPoint t) = 0) (u : ℝ) : kernel n t u = 0 := by
  rw [kernel_factorization]
  exact envelope_row_zero_of_zero zetaEnvelope (core n)
    (by simp [zetaEnvelope, ht]) u

/-- Exact cancellation in the normalized two-point expression. This alone
does not identify a point process with Montgomery's zero statistics. -/
theorem normalized_pair_correlation (n : ℕ) (t u : ℝ)
    (ht : riemannZeta (criticalPoint t) ≠ 0)
    (hu : riemannZeta (criticalPoint u) ≠ 0)
    (hAt : (core n t t).re ≠ 0) (hAu : (core n u u).re ≠ 0) :
    pairDensity (kernel n) t u / ((kernel n t t).re * (kernel n u u).re) =
      1 - ‖core n t u‖ ^ 2 / ((core n t t).re * (core n u u).re) := by
  rw [kernel_eq_envelope]
  exact normalized_pairDensity_envelope zetaEnvelope (core n) t u
    (div_ne_zero ht (criticalPoint_ne_zero t))
    (div_ne_zero hu (criticalPoint_ne_zero u)) hAt hAu

end RiemannResearch.RH.Pareto.MellinFrequency
