/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.GapKernelFourierScaling
import RiemannResearch.Analysis.GapKernelObjective

noncomputable section
namespace RiemannResearch.Analysis.GapKernelFourierGaussian
open GapKernelPolynomial

/-- The radius parametrization used to certify the moment objective gives
the same scaled function as the Fourier-normalized Gaussian model. -/
theorem normalizedTest_eq_objectiveTest (p q : List ℤ) {r θ : ℝ}
    (hr : 0 < r) (hθ : 0 < θ) (hq : 0 < value q 0) :
    normalizedTest p q (θ*Real.sqrt Real.pi/r) =
      GapKernelObjective.test r θ (value q 0) (value p) := by
  funext x
  have hroot : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have ha : Real.pi * (x / (θ * Real.sqrt Real.pi / r))^2 = ((r / θ) * x)^2 := by
    calc
      _ = (Real.sqrt Real.pi * (x / (θ * Real.sqrt Real.pi / r)))^2 := by
        rw [mul_pow, Real.sq_sqrt Real.pi_pos.le]
      _ = _ := by congr 1; field_simp [hroot, hr.ne', hθ.ne'] <;> ring
  simp only [normalizedTest, model, GapKernelObjective.test, neg_mul, ha]
  field_simp [hroot, hr.ne', hθ.ne', hq.ne'] <;> ring

end RiemannResearch.Analysis.GapKernelFourierGaussian
