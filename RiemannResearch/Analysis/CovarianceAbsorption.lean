import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Covariance absorption and finite energy bounds

Source: user-requested Route 6 covariance continuation, 2026-09-20.
These elementary ordered-real arguments formalize only the summation step.
The intended RH application uses the compensated Chebyshev square identity.
No declaration here proves that identity for integrals, the arithmetic
covariance estimate, weighted integrability, or RH. Those are separate inputs.
-/

open scoped BigOperators
namespace RiemannResearch.Analysis.CovarianceAbsorption

/-- Telescoping retains the final boundary and every signed covariance input. -/
theorem finite_absorption_bound
    (s η : ℝ) (I B D C a : ℕ → ℝ)
    (hid : ∀ k, s * I k + B (k + 1) = B k + D k + 2 * C k)
    (hcov : ∀ k, C k ≤ (s / 2 - η) * I k + a k) (N : ℕ) :
    2 * η * (∑ k ∈ Finset.range N, I k) + B N ≤
      B 0 + (∑ k ∈ Finset.range N, D k) +
        2 * (∑ k ∈ Finset.range N, a k) := by
  induction N with
  | zero => simp
  | succ N ih =>
      simp only [Finset.sum_range_succ]
      have hstep : 2 * η * I N + B (N + 1) ≤ B N + D N + 2 * a N := by
        have hi := hid N
        have hc := hcov N
        nlinarith
      nlinarith

/-- A positive margin and bounded error sums give a uniform partial-energy bound. -/
theorem partial_energy_bound
    (s η Dmax Amax : ℝ) (I B D C a : ℕ → ℝ)
    (hη : 0 < η) (hB : ∀ k, 0 ≤ B k)
    (hid : ∀ k, s * I k + B (k + 1) = B k + D k + 2 * C k)
    (hcov : ∀ k, C k ≤ (s / 2 - η) * I k + a k)
    (hD : ∀ N, (∑ k ∈ Finset.range N, D k) ≤ Dmax)
    (ha : ∀ N, (∑ k ∈ Finset.range N, a k) ≤ Amax) (N : ℕ) :
    (∑ k ∈ Finset.range N, I k) ≤ (B 0 + Dmax + 2 * Amax) / (2 * η) := by
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * η)).2
  have h := finite_absorption_bound s η I B D C a hid hcov N
  have hb := hB N
  have hd := hD N
  have he := ha N
  nlinarith

/-- Cofinal nonpositive covariance bounds a monotone energy sequence. -/
theorem cofinal_nonpositive_covariance_bound
    (s Dmax : ℝ) (I B D C : ℕ → ℝ)
    (hs : 0 < s) (hI : Monotone I) (hB : ∀ n, 0 ≤ B n)
    (hD : ∀ n, D n ≤ Dmax)
    (hid : ∀ n, s * I n + B n = 1 + D n + 2 * C n)
    (hcov : ∀ N, ∃ n, N ≤ n ∧ C n ≤ 0) (N : ℕ) :
    I N ≤ (1 + Dmax) / s := by
  obtain ⟨n, hNn, hc⟩ := hcov N
  apply (le_div_iff₀ hs).2
  have hi := hI hNn
  have hb := hB n
  have hd := hD n
  have he := hid n
  nlinarith

end RiemannResearch.Analysis.CovarianceAbsorption
