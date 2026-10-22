import RiemannResearch.Analysis.LogarithmicSamplingBounds
import RiemannResearch.Analysis.WeightedBalancedSampling

/-!
# Balanced logarithmic sampling with positive weighted arithmetic rows

The logarithmic `2*q` moment is the proved `(4*q)! * X * (X+1)` estimate.
Only the actual entry-error envelope, arithmetic-kernel norm symmetry, and
the positive weighted arithmetic row budgets remain provider hypotheses.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.LogarithmicSamplingBounds

open ZeroSamplingQuadratic

/-- The balanced higher-power bound with a proved logarithmic moment and the
correct weighted arithmetic rows. The result is uniform in all coefficients. -/
theorem logarithmic_power_kernel_positive_weighted (X : ℕ)
    (S B : ℕ → ℕ → ℂ) (a : ℕ → ℂ) (w : ℕ → ℝ)
    (q : ℕ) (hq : 2 ≤ q) (d L η K_A K_0 : ℝ)
    (hd : 0 ≤ d) (hL : 0 < L) (hη : 0 ≤ η)
    (herror : ∀ n ∈ (Finset.Icc 1 X : Finset ℕ),
      ∀ m ∈ (Finset.Icc 1 X : Finset ℕ),
        ‖S n m - B n m‖ ≤
          d / L * Real.log ((n : ℝ) / (m : ℝ)) ^ 2 + η)
    (hsymB : ∀ n ∈ (Finset.Icc 1 X : Finset ℕ),
      ∀ m ∈ (Finset.Icc 1 X : Finset ℕ), ‖B n m‖ = ‖B m n‖)
    (hw : ∀ n ∈ (Finset.Icc 1 X : Finset ℕ), 0 < w n)
    (hrowA : ∀ n ∈ (Finset.Icc 1 X : Finset ℕ),
      (∑ m ∈ (Finset.Icc 1 X : Finset ℕ),
        (‖B n m‖ ^ (q - 1) * Real.log ((n : ℝ) / (m : ℝ)) ^ 2) * w m) ≤
          K_A * w n)
    (hrow0 : ∀ n ∈ (Finset.Icc 1 X : Finset ℕ),
      (∑ m ∈ (Finset.Icc 1 X : Finset ℕ), ‖B n m‖ ^ (q - 1) * w m) ≤
        K_0 * w n) :
    ‖form (Finset.Icc 1 X : Finset ℕ)
        (fun (n m : ℕ) => (‖S n m‖ ^ q : ℂ)) a -
      form (Finset.Icc 1 X : Finset ℕ)
        (fun (n m : ℕ) => (‖B n m‖ ^ q : ℂ)) a‖ ≤
      ((q : ℝ) * (2 : ℝ) ^ (q - 2)) *
        (d / L * K_A + η * K_0 + (2 : ℝ) ^ (q - 1) *
          ((d / L) ^ q *
            Real.sqrt (((4 * q).factorial : ℝ) * (X : ℝ) * ((X : ℝ) + 1)) +
            (X : ℝ) * η ^ q)) *
        coefficientEnergy (Finset.Icc 1 X : Finset ℕ) a := by
  have h := structured_power_kernel_positive_weighted
    (Finset.Icc 1 X : Finset ℕ) S B a logSquareEnvelope w q hq d L η K_A K_0
    (((4 * q).factorial : ℝ) * (X : ℝ) * ((X : ℝ) + 1)) hd hL hη
    (fun (n : ℕ) _ (m : ℕ) _ => logSquareEnvelope_nonneg n m)
    herror hsymB
    (fun (n : ℕ) _ (m : ℕ) _ => logSquareEnvelope_symm n m)
    hw hrowA hrow0 (logSquareEnvelope_even_moment q X)
  have hcard : (((Finset.Icc 1 X : Finset ℕ).card) : ℝ) = (X : ℝ) := by simp
  simpa only [hcard] using h

end RiemannResearch.Analysis.LogarithmicSamplingBounds
