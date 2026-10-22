import RiemannResearch.Analysis.ScaledKernelDerivative
import RiemannResearch.Analysis.BroadKernelUniformBounds

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# The broad profile derivative array is the actual derivative tower

Differentiation is taken through the actual convolution integral and then
through its four explicit coefficients. Division by the normalization is
constant in the spatial variable, including its totalized zero case.
-/

open MeasureTheory

namespace RiemannResearch.Analysis

theorem hasDerivAt_broadKernelProfile (h : ℝ → ℝ) (f : ℕ → ℝ → ℝ)
    (hh : Integrable h) (hfd : ∀ j, Differentiable ℝ (f j))
    (hnext : ∀ j, deriv (f j) = f (j + 1))
    (M : ℕ → ℝ) (hM : ∀ j x, |f j x| ≤ M j) (R x : ℝ) :
    HasDerivAt (broadKernelProfile h f R)
      (broadKernelProfile h (fun j => f (j + 1)) R x) x := by
  have hd (j : ℕ) : HasDerivAt (scaledKernelConvolution h (f j) R)
      (scaledKernelConvolution h (f (j + 1)) R x) x := by
    have hdc : Continuous (deriv (f j)) := by
      rw [hnext j]
      exact (hfd (j + 1)).continuous
    have hb : ∀ y, |deriv (f j) y| ≤ M (j + 1) := by
      rw [hnext j]
      exact hM (j + 1)
    simpa only [hnext j] using hasDerivAt_scaledKernelConvolution h (f j) hh
      (hfd j) hdc (M j) (M (j + 1)) (hM j) hb R x
  exact ((((hd 3).const_mul ((R⁻¹)^3)).add ((hd 2).const_mul ((R⁻¹)^2/2))).sub
    ((hd 1).const_mul (R⁻¹/4))).sub ((hd 0).const_mul (1/8))

theorem deriv_broadKernelProfile (h : ℝ → ℝ) (f : ℕ → ℝ → ℝ)
    (hh : Integrable h) (hfd : ∀ j, Differentiable ℝ (f j))
    (hnext : ∀ j, deriv (f j) = f (j + 1))
    (M : ℕ → ℝ) (hM : ∀ j x, |f j x| ≤ M j) (R : ℝ) :
    deriv (broadKernelProfile h f R) = broadKernelProfile h (fun j => f (j + 1)) R := by
  funext x
  exact (hasDerivAt_broadKernelProfile h f hh hfd hnext M hM R x).deriv

theorem hasDerivAt_normalizedBroadKernelDerivative (h : ℝ → ℝ)
    (f : ℕ → ℝ → ℝ) (hh : Integrable h) (hfd : ∀ j, Differentiable ℝ (f j))
    (hnext : ∀ j, deriv (f j) = f (j + 1))
    (M : ℕ → ℝ) (hM : ∀ j x, |f j x| ≤ M j) (j : ℕ) (R x : ℝ) :
    HasDerivAt (normalizedBroadKernelDerivative h f j R)
      (normalizedBroadKernelDerivative h f (j + 1) R x) x := by
  have hshift (k : ℕ) : deriv (f (k+j)) = f ((k+1)+j) := by
    simpa only [Nat.add_assoc, Nat.add_comm 1 j] using (hnext (k+j))
  have hd := (hasDerivAt_broadKernelProfile h (fun k => f (k+j)) hh
    (fun k => hfd (k+j)) hshift (fun k => M (k+j)) (fun k => hM (k+j)) R x).div_const
      (broadKernelNorm h f R)
  have he : (fun k => f ((k+1)+j)) = (fun k => f (k+(j+1))) := by
    funext k
    congr 1
    omega
  rw [he] at hd
  convert hd using 1 <;> rfl

theorem iteratedDeriv_normalizedBroadKernelProfile (h : ℝ → ℝ)
    (f : ℕ → ℝ → ℝ) (hh : Integrable h) (hfd : ∀ j, Differentiable ℝ (f j))
    (hnext : ∀ j, deriv (f j) = f (j + 1))
    (M : ℕ → ℝ) (hM : ∀ j x, |f j x| ≤ M j) (j : ℕ) (R : ℝ) :
    iteratedDeriv j (normalizedBroadKernelProfile h f R) =
      normalizedBroadKernelDerivative h f j R := by
  induction j with
  | zero =>
      rw [iteratedDeriv_zero]
      rfl
  | succ j ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      exact (hasDerivAt_normalizedBroadKernelDerivative h f hh hfd hnext M hM j R x).deriv

end RiemannResearch.Analysis
