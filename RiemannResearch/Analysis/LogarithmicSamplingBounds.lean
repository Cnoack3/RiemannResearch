import RiemannResearch.Analysis.LogarithmicMatrixMoments
import RiemannResearch.Analysis.ZeroSamplingHilbertSchmidt
import RiemannResearch.Analysis.WeightedSamplingSchur

/-!
# Sampling transfer with proved logarithmic matrix budgets

These specializations use the actual squared logarithmic ratio on `1..X`.
Only the Fourier entry error and the displayed arithmetic row budgets remain
as provider hypotheses; the second and fourth matrix budgets are the proved
factorial logarithmic moments.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.LogarithmicSamplingBounds

open ZeroSamplingQuadratic LogarithmicMatrixMoments

/-- The real, nonnegative squared logarithmic ratio envelope. -/
def logSquareEnvelope (n m : ℕ) : ℝ := Real.log ((n : ℝ) / (m : ℝ)) ^ 2

theorem logSquareEnvelope_nonneg (n m : ℕ) : 0 ≤ logSquareEnvelope n m :=
  sq_nonneg _

theorem logSquareEnvelope_symm (n m : ℕ) :
    logSquareEnvelope n m = logSquareEnvelope m n := by
  unfold logSquareEnvelope
  calc
    _ = |Real.log ((n : ℝ) / (m : ℝ))| ^ 2 := (sq_abs _).symm
    _ = |Real.log ((m : ℝ) / (n : ℝ))| ^ 2 :=
      congrArg (fun x : ℝ => x ^ 2) (abs_log_div_symm (n : ℝ) (m : ℝ))
    _ = _ := sq_abs _

/-- The exact `2k`-moment of the squared logarithmic envelope. -/
theorem logSquareEnvelope_even_moment (k X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, ∑ m ∈ Finset.Icc 1 X,
      logSquareEnvelope n m ^ (2 * k)) ≤
        ((4 * k).factorial : ℝ) * (X : ℝ) * ((X : ℝ) + 1) := by
  have h := double_even_log_moment (2 * k) X
  simp only [pow_abs_two_mul] at h
  have he : 2 * (2 * k) = 4 * k := by omega
  simpa only [logSquareEnvelope, ← pow_mul, he] using h

theorem logSquareEnvelope_second_moment (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, ∑ m ∈ Finset.Icc 1 X,
      logSquareEnvelope n m ^ 2) ≤ 24 * (X : ℝ) * ((X : ℝ) + 1) := by
  simpa [Nat.factorial] using logSquareEnvelope_even_moment 1 X

theorem logSquareEnvelope_fourth_moment (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, ∑ m ∈ Finset.Icc 1 X,
      logSquareEnvelope n m ^ 4) ≤ 40320 * (X : ℝ) * ((X : ℝ) + 1) := by
  simpa [Nat.factorial] using logSquareEnvelope_even_moment 2 X

/-- The single sampling form bound with no supplied logarithmic moment
hypothesis.  It is uniform over every complex coefficient family on `1..X`. -/
theorem logarithmic_hilbertSchmidt_single (X : ℕ)
    (S H : ℕ → ℕ → ℂ) (a : ℕ → ℂ) (d L η : ℝ)
    (hd : 0 ≤ d) (hL : 0 < L) (hη : 0 ≤ η)
    (hentry : ∀ n ∈ Finset.Icc 1 X, ∀ m ∈ Finset.Icc 1 X,
      ‖S n m - H n m‖ ≤ d / L * logSquareEnvelope n m + η) :
    ‖form (Finset.Icc 1 X) S a - form (Finset.Icc 1 X) H a‖ ≤
      (d * Real.sqrt (24 * (X : ℝ) * ((X : ℝ) + 1)) / L + η * (X : ℝ)) *
        coefficientEnergy (Finset.Icc 1 X) a := by
  simpa using logarithmic_norm_envelope_transfer (Finset.Icc 1 X) S H a
    d L (X : ℝ) η logSquareEnvelope hd hL hη
    (fun n _ m _ => logSquareEnvelope_nonneg n m) hentry
    (logSquareEnvelope_second_moment X)

/-- The pair covariance bound with positive weighted arithmetic rows.
The mixed remainder is retained exactly, with the proved `4!` and `8!`
logarithmic matrix moments. -/
theorem logarithmic_square_kernel_weighted_exact_cross (X : ℕ)
    (S B : ℕ → ℕ → ℂ) (a : ℕ → ℂ) (w : ℕ → ℝ)
    (d L η KA K0 : ℝ)
    (hd : 0 ≤ d) (hL : 0 < L) (hη : 0 ≤ η)
    (hBsym : ∀ n ∈ Finset.Icc 1 X, ∀ m ∈ Finset.Icc 1 X,
      ‖B n m‖ = ‖B m n‖)
    (hw : ∀ n ∈ Finset.Icc 1 X, 0 < w n)
    (herror : ∀ n ∈ Finset.Icc 1 X, ∀ m ∈ Finset.Icc 1 X,
      ‖S n m - B n m‖ ≤ d / L * logSquareEnvelope n m + η)
    (hrowA : ∀ n ∈ Finset.Icc 1 X,
      (∑ m ∈ Finset.Icc 1 X, (‖B n m‖ * logSquareEnvelope n m) * w m) ≤
        KA * w n)
    (hrow0 : ∀ n ∈ Finset.Icc 1 X,
      (∑ m ∈ Finset.Icc 1 X, ‖B n m‖ * w m) ≤ K0 * w n) :
    ‖form (Finset.Icc 1 X) (fun n m => (‖S n m‖ ^ 2 : ℂ)) a -
        form (Finset.Icc 1 X) (fun n m => (‖B n m‖ ^ 2 : ℂ)) a‖ ≤
      (2 * (d / L) * KA + 2 * η * K0 +
        (d / L) ^ 2 * Real.sqrt (40320 * (X : ℝ) * ((X : ℝ) + 1)) +
        2 * (d / L) * η * Real.sqrt (24 * (X : ℝ) * ((X : ℝ) + 1)) +
        η ^ 2 * (X : ℝ)) * coefficientEnergy (Finset.Icc 1 X) a := by
  simpa using square_kernel_weighted_arithmetic_transfer_exact_cross
    (Finset.Icc 1 X) S B a logSquareEnvelope w (d / L) η KA K0
    (24 * (X : ℝ) * ((X : ℝ) + 1))
    (40320 * (X : ℝ) * ((X : ℝ) + 1))
    (div_nonneg hd hL.le) hη
    (fun n _ m _ => logSquareEnvelope_nonneg n m)
    (fun n _ m _ => logSquareEnvelope_symm n m)
    hBsym hw herror hrowA hrow0
    (logSquareEnvelope_second_moment X) (logSquareEnvelope_fourth_moment X)

end RiemannResearch.Analysis.LogarithmicSamplingBounds
