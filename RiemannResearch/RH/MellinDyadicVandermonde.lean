import RiemannResearch.Analysis.PowerDifferenceDeterminant
import RiemannResearch.RH.MellinDPPIntensity
import RiemannResearch.RH.MellinFrequencyKernel

/-!
# Exact dyadic Mellin minors and their zero sets

Source: the dyadic determinant derivation in `DyadicDysonConnection20260928.md`.
This module verifies its algebraic core and the actual Mellin-minor zero-set
criterion. Folding, sine universality, and operator analysis remain paper proofs.
No RH, zero-simplicity, or inverse-Gram growth hypothesis is used.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.MellinFrequency

def dyadicPhase (t : ℝ) : ℂ := (2 : ℂ)^(-criticalPoint t)

private theorem dyadic_cpow (s : ℂ) (k : ℕ) :
    ((2 : ℂ)^k)^(-s) = ((2 : ℂ)^(-s))^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hm := Complex.mul_cpow_ofReal_nonneg (a := (2 : ℝ)^k) (b := 2)
      (by positivity) (by norm_num) (-s)
    push_cast at hm
    calc
      ((2 : ℂ)^(k+1))^(-s) = ((2 : ℂ)^k*2)^(-s) := by rw [pow_succ]
      _ = ((2 : ℂ)^k)^(-s) * (2 : ℂ)^(-s) := hm
      _ = ((2 : ℂ)^(-s))^(k+1) := by rw [ih, pow_succ]

/-- The actual residue symbol at a dyadic conductor is a difference of powers. -/
theorem residueSymbol_dyadic (k : ℕ) (t : ℝ) :
    residueSymbol (2^(k+1)-2) t = (1/2 : ℂ)^(k+1) - dyadicPhase t^(k+1) := by
  have hp : 0 < (2 : ℕ)^k := pow_pos (by norm_num) _
  have htwo : 2 ≤ (2 : ℕ)^(k+1) := by rw [pow_succ]; omega
  unfold residueSymbol dyadicPhase
  rw [Nat.sub_add_cancel htwo]
  push_cast
  rw [dyadic_cpow]
  simp only [div_pow, one_pow]

/-- The m by m symbol minor using conductors 2,4,...,2^m. -/
def dyadicSymbolMatrix (m : ℕ) (t : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of (fun i j => residueSymbol (2^(j.val+1)-2) (t i))

theorem dyadicSymbolMatrix_det_vandermonde (m : ℕ) (t : Fin m → ℝ) :
    (dyadicSymbolMatrix m t).det =
      (∏ i : Fin m, ((1/2 : ℂ)-dyadicPhase (t i))) *
        (Matrix.vandermonde (fun i => dyadicPhase (t i))).det := by
  unfold dyadicSymbolMatrix
  simp_rw [residueSymbol_dyadic]
  exact RiemannResearch.Analysis.powerDifference_det_vandermonde m (1/2 : ℂ)
    (fun i => dyadicPhase (t i))

theorem dyadicSymbolMatrix_det (m : ℕ) (t : Fin m → ℝ) :
    (dyadicSymbolMatrix m t).det =
      (∏ i : Fin m, ((1/2 : ℂ)-dyadicPhase (t i))) *
        ∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (dyadicPhase (t j)-dyadicPhase (t i)) := by
  rw [dyadicSymbolMatrix_det_vandermonde, Matrix.det_vandermonde]

/-- Dyadic aliases are the only cause of degeneracy of this symbol minor. -/
theorem dyadicSymbolMatrix_det_ne_zero_iff (m : ℕ) (t : Fin m → ℝ) :
    (dyadicSymbolMatrix m t).det ≠ 0 ↔
      Function.Injective (fun i => dyadicPhase (t i)) := by
  have hprod : (∏ i : Fin m, ((1/2 : ℂ)-dyadicPhase (t i))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    simpa [residueSymbol, dyadicPhase] using residueSymbol_zero_ne_zero (t i)
  rw [dyadicSymbolMatrix_det_vandermonde, mul_ne_zero_iff,
    Matrix.det_vandermonde_ne_zero_iff]
  exact and_iff_right hprod

/-- Actual Mellin feature minor on the same dyadic conductors. -/
def dyadicMellinMatrix (m : ℕ) (t : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of (fun i j => paretoMellin
    (CoefficientStabilization.residueAtom (2^(j.val+1)-2)) (criticalPoint (t i)))

theorem dyadicMellinMatrix_det_factorization (m : ℕ) (t : Fin m → ℝ) :
    (dyadicMellinMatrix m t).det =
      (∏ i : Fin m, zetaEnvelope (t i)) * (dyadicSymbolMatrix m t).det := by
  have he : dyadicMellinMatrix m t =
      Matrix.of (fun i j => zetaEnvelope (t i) * dyadicSymbolMatrix m t i j) := by
    ext i j
    exact residueAtom_transform (2^(j.val+1)-2) (t i)
  rw [he, Matrix.det_mul_column]

/-- Complete zero-set characterization of every actual dyadic Mellin minor:
only a sampled zeta zero or a repeated dyadic phase can make it singular. -/
theorem dyadicMellinMatrix_det_ne_zero_iff (m : ℕ) (t : Fin m → ℝ) :
    (dyadicMellinMatrix m t).det ≠ 0 ↔
      (∀ i, riemannZeta (criticalPoint (t i)) ≠ 0) ∧
        Function.Injective (fun i => dyadicPhase (t i)) := by
  have henv : (∏ i : Fin m, zetaEnvelope (t i)) ≠ 0 ↔
      ∀ i, riemannZeta (criticalPoint (t i)) ≠ 0 := by
    constructor
    · intro he i hzero
      have hi := Finset.prod_ne_zero_iff.mp he i (Finset.mem_univ i)
      apply hi
      simp [zetaEnvelope, hzero]
    · intro hi
      exact Finset.prod_ne_zero_iff.mpr
        (fun i _ => div_ne_zero (hi i) (criticalPoint_ne_zero (t i)))
  rw [dyadicMellinMatrix_det_factorization, mul_ne_zero_iff, henv,
    dyadicSymbolMatrix_det_ne_zero_iff]

end RiemannResearch.RH.Pareto.MellinFrequency
