import RiemannResearch.Analysis.LogarithmicSamplingBounds
import RiemannResearch.Analysis.BalancedSamplingErrorTransfer

/-!
# Balanced sampling bounds with proved logarithmic moment budgets

The logarithmic moments in these finite comparison bounds are supplied by
`LogarithmicMatrixMoments`, rather than retained as analytic hypotheses.
The hypotheses are the entry error envelope, symmetry of the arithmetic
kernel norm, and its two unweighted arithmetic row budgets.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.LogarithmicSamplingBounds

open ZeroSamplingQuadratic

/-- A higher-power balanced comparison with no logarithmic moment premise.
All arithmetic row sums remain unweighted by the coefficients `a`. -/
theorem logarithmic_power_kernel_form_comparison (X : ℕ)
    (S B : ℕ → ℕ → ℂ) (a : ℕ → ℂ)
    (q : ℕ) (hq : 2 ≤ q) (d L η K_A K_0 : ℝ)
    (hd : 0 ≤ d) (hL : 0 < L) (hη : 0 ≤ η)
    (herror : ∀ n ∈ (Finset.Icc 1 X : Finset ℕ),
      ∀ m ∈ (Finset.Icc 1 X : Finset ℕ),
        ‖S n m - B n m‖ ≤
          d / L * Real.log ((n : ℝ) / (m : ℝ)) ^ 2 + η)
    (hsymB : ∀ n ∈ (Finset.Icc 1 X : Finset ℕ),
      ∀ m ∈ (Finset.Icc 1 X : Finset ℕ), ‖B n m‖ = ‖B m n‖)
    (hrowA : ∀ n ∈ (Finset.Icc 1 X : Finset ℕ),
      (∑ m ∈ (Finset.Icc 1 X : Finset ℕ),
        ‖B n m‖ ^ (q - 1) * Real.log ((n : ℝ) / (m : ℝ)) ^ 2) ≤ K_A)
    (hrow0 : ∀ n ∈ (Finset.Icc 1 X : Finset ℕ),
      (∑ m ∈ (Finset.Icc 1 X : Finset ℕ), ‖B n m‖ ^ (q - 1)) ≤ K_0) :
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
  have h := structured_power_kernel_form_comparison
    (Finset.Icc 1 X : Finset ℕ) S B a logSquareEnvelope q hq d L η K_A K_0
    (((4 * q).factorial : ℝ) * (X : ℝ) * ((X : ℝ) + 1)) hd hL hη
    (fun (n : ℕ) _ (m : ℕ) _ => logSquareEnvelope_nonneg n m)
    herror hsymB
    (fun (n : ℕ) _ (m : ℕ) _ => logSquareEnvelope_symm n m)
    hrowA hrow0 (logSquareEnvelope_even_moment q X)
  have hcard : (((Finset.Icc 1 X : Finset ℕ).card) : ℝ) = (X : ℝ) := by simp
  simpa only [hcard] using h

/-- The sharp square comparison uses the eighth logarithmic moment and its
factorial `8!` budget, preserving the exact linear coefficient two. -/
theorem logarithmic_square_kernel_form_comparison (X : ℕ)
    (S B : ℕ → ℕ → ℂ) (a : ℕ → ℂ) (d L η K_A K_0 : ℝ)
    (hd : 0 ≤ d) (hL : 0 < L) (hη : 0 ≤ η)
    (herror : ∀ n ∈ (Finset.Icc 1 X : Finset ℕ),
      ∀ m ∈ (Finset.Icc 1 X : Finset ℕ),
        ‖S n m - B n m‖ ≤
          d / L * Real.log ((n : ℝ) / (m : ℝ)) ^ 2 + η)
    (hsymB : ∀ n ∈ (Finset.Icc 1 X : Finset ℕ),
      ∀ m ∈ (Finset.Icc 1 X : Finset ℕ), ‖B n m‖ = ‖B m n‖)
    (hrowA : ∀ n ∈ (Finset.Icc 1 X : Finset ℕ),
      (∑ m ∈ (Finset.Icc 1 X : Finset ℕ),
        ‖B n m‖ * Real.log ((n : ℝ) / (m : ℝ)) ^ 2) ≤ K_A)
    (hrow0 : ∀ n ∈ (Finset.Icc 1 X : Finset ℕ),
      (∑ m ∈ (Finset.Icc 1 X : Finset ℕ), ‖B n m‖) ≤ K_0) :
    ‖form (Finset.Icc 1 X : Finset ℕ)
        (fun (n m : ℕ) => (‖S n m‖ ^ 2 : ℂ)) a -
      form (Finset.Icc 1 X : Finset ℕ)
        (fun (n m : ℕ) => (‖B n m‖ ^ 2 : ℂ)) a‖ ≤
      (2 * (d / L) * K_A + 2 * η * K_0 +
        2 * (d / L) ^ 2 *
          Real.sqrt ((Nat.factorial 8 : ℝ) * (X : ℝ) * ((X : ℝ) + 1)) +
        2 * (X : ℝ) * η ^ 2) *
      coefficientEnergy (Finset.Icc 1 X : Finset ℕ) a := by
  have hmoment : (∑ n ∈ (Finset.Icc 1 X : Finset ℕ),
      ∑ m ∈ (Finset.Icc 1 X : Finset ℕ), logSquareEnvelope n m ^ 4) ≤
      (Nat.factorial 8 : ℝ) * (X : ℝ) * ((X : ℝ) + 1) := by
    simpa only [show 2 * (2 : ℕ) = 4 from rfl, show 4 * (2 : ℕ) = 8 from rfl]
      using logSquareEnvelope_even_moment 2 X
  have h := structured_square_kernel_form_comparison
    (Finset.Icc 1 X : Finset ℕ) S B a logSquareEnvelope d L η K_A K_0
    ((Nat.factorial 8 : ℝ) * (X : ℝ) * ((X : ℝ) + 1)) hd hL hη
    (fun (n : ℕ) _ (m : ℕ) _ => logSquareEnvelope_nonneg n m)
    herror hsymB
    (fun (n : ℕ) _ (m : ℕ) _ => logSquareEnvelope_symm n m)
    hrowA hrow0 hmoment
  have hcard : (((Finset.Icc 1 X : Finset ℕ).card) : ℝ) = (X : ℝ) := by simp
  simpa only [hcard] using h

end RiemannResearch.Analysis.LogarithmicSamplingBounds
