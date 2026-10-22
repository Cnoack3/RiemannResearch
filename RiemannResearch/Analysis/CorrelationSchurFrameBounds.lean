/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Matrix.Order

/-!
# Correlation Schur transport of finite frame bounds

The Schur product theorem `Matrix.PosSemidef.hadamard` transports both
PSD frame bounds with their constants unchanged when the correlation diagonal
is one. Concrete RH consumer: the Cauchy smoothing reduction described in
`../RH/CauchySmoothedActualZeroFrames20261005.md`. The actual Cauchy-kernel
and Fourier specialization are separate paper proofs.
-/

namespace Matrix

open scoped Matrix ComplexOrder

variable {ι : Type*}

private theorem hadamard_sub_right (S A B : Matrix ι ι ℂ) :
    S ⊙ (A - B) = S ⊙ A - S ⊙ B := by
  ext i j
  simp only [Matrix.hadamard_apply, Matrix.sub_apply, mul_sub]

variable [DecidableEq ι]

/-- A correlation Schur multiplier preserves the identity matrix. -/
theorem correlation_hadamard_one (S : Matrix ι ι ℂ)
    (hdiag : ∀ i, S i i = 1) : S ⊙ (1 : Matrix ι ι ℂ) = 1 := by
  apply Matrix.hadamard_one_eq_one_iff.mpr
  funext i
  exact hdiag i

variable [Fintype ι]

/-- Lower PSD frame bounds pass to a correlation Schur multiplier. -/
theorem correlation_lower_psd (S H : Matrix ι ι ℂ) (r : ℝ)
    (hS : S.PosSemidef) (hdiag : ∀ i, S i i = 1)
    (hLower : (H - r • (1 : Matrix ι ι ℂ)).PosSemidef) :
    (S ⊙ H - r • (1 : Matrix ι ι ℂ)).PosSemidef := by
  have h := hS.hadamard hLower
  rw [hadamard_sub_right, Matrix.hadamard_smul,
    correlation_hadamard_one S hdiag] at h
  exact h

/-- Upper PSD frame bounds pass to a correlation Schur multiplier. -/
theorem correlation_upper_psd (S H : Matrix ι ι ℂ) (r : ℝ)
    (hS : S.PosSemidef) (hdiag : ∀ i, S i i = 1)
    (hUpper : (r • (1 : Matrix ι ι ℂ) - H).PosSemidef) :
    (r • (1 : Matrix ι ι ℂ) - S ⊙ H).PosSemidef := by
  have h := hS.hadamard hUpper
  rw [hadamard_sub_right, Matrix.hadamard_smul,
    correlation_hadamard_one S hdiag] at h
  exact h

/-- Both finite frame bounds pass with their constants unchanged. -/
theorem correlation_frame_psd_bounds (S H : Matrix ι ι ℂ)
    (lo hi : ℝ) (hS : S.PosSemidef) (hdiag : ∀ i, S i i = 1)
    (hLower : (H - lo • (1 : Matrix ι ι ℂ)).PosSemidef)
    (hUpper : (hi • (1 : Matrix ι ι ℂ) - H).PosSemidef) :
    (S ⊙ H - lo • (1 : Matrix ι ι ℂ)).PosSemidef ∧
      (hi • (1 : Matrix ι ι ℂ) - S ⊙ H).PosSemidef :=
  ⟨correlation_lower_psd S H lo hS hdiag hLower,
    correlation_upper_psd S H hi hS hdiag hUpper⟩

end Matrix
