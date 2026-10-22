import RiemannResearch.Analysis.ActualZeroOrdinate
import RiemannResearch.Analysis.HorizontalPhaseBootstrap
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Tactic.Ring

/-!
# Exact horizontal even series for actual zeta zeros

The actual scalar correction is its complete positive even Taylor series.
The finite cutoff contains every analytic multiplicity and keeps the original
weights. The helper belongs to the generic Complex namespace. No Landau,
zero-density or RH hypothesis occurs in these identities.
Source: the user-provided phase-Gram argument; the convergent real cosh series
is supplied by HorizontalPhaseBootstrap and Mathlib's trigonometric series.
-/

noncomputable section
open Complex Zeta23
open scoped BigOperators
namespace Complex
open RiemannResearch.Analysis.HorizontalPhaseBootstrap

/-- The positive even part of the actual real cosh series, in complex scalars. -/
theorem hasSum_even_cosh_correction (u a : ℝ) (c : ℂ) :
    HasSum (fun k : ℕ => ((Nat.factorial (2 * (k + 1)) : ℂ)⁻¹) *
      (u : ℂ) ^ (2 * (k + 1)) * (c * (a : ℂ) ^ (2 * (k + 1))))
      (c * ((Real.cosh (u * a) : ℂ) - 1)) := by
  have hr := (cosh_tail_summable (u * a)).hasSum
  rw [cosh_tail_tsum] at hr
  have hc := (Complex.ofRealCLM.hasSum hr).mul_left c
  simp only [Complex.ofRealCLM_apply, Complex.ofReal_sub, Complex.ofReal_one] at hc
  convert hc using 1 <;> try rfl
  · funext k
    simp only [Complex.ofReal_div, Complex.ofReal_pow,
      Complex.ofReal_mul, Complex.ofReal_natCast]
    rw [mul_pow]
    ring

end Complex

namespace RiemannResearch.Analysis.ActualZeroOrdinate
open ZeroOrdinate HorizontalPhaseBootstrap

theorem weightedCoshCorrection_hasSum_evenMoments (T u : ℝ) (w : ℂ → ℂ) :
    HasSum (fun k : ℕ => ((Nat.factorial (2 * (k + 1)) : ℂ)⁻¹) *
      (u : ℂ) ^ (2 * (k + 1)) *
      sum T (fun ρ => w ρ * phase u ρ.im *
        ((ρ.re - 1 / 2 : ℝ) : ℂ) ^ (2 * (k + 1))))
      (weightedCoshCorrection T u w) := by
  classical
  have hs := hasSum_sum (s := cutoff T)
    (fun ρ _ => (Complex.hasSum_even_cosh_correction u (ρ.re - 1 / 2)
      ((zeroMult ρ : ℂ) * w ρ * phase u ρ.im)))
  convert hs using 1
  · funext k
    unfold sum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ρ _
    ring
  · unfold weightedCoshCorrection sum
    apply Finset.sum_congr rfl
    intro ρ _
    ring

theorem weightedCoshCorrection_eq_tsum_evenMoments (T u : ℝ) (w : ℂ → ℂ) :
    weightedCoshCorrection T u w =
      ∑' k : ℕ, ((Nat.factorial (2 * (k + 1)) : ℂ)⁻¹) *
      (u : ℂ) ^ (2 * (k + 1)) *
      sum T (fun ρ => w ρ * phase u ρ.im *
        ((ρ.re - 1 / 2 : ℝ) : ℂ) ^ (2 * (k + 1))) :=
  (weightedCoshCorrection_hasSum_evenMoments T u w).tsum_eq.symm
end RiemannResearch.Analysis.ActualZeroOrdinate
