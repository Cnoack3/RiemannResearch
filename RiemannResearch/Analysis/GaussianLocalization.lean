import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Summable Gaussian localization with a signed lower bound

These estimates abstract the zero-side Gaussian localization used in the
signed explicit-formula matrix investigation of 29 October 2026. They verify
the infinite-series estimate from explicit summability and exponent hypotheses.
They do not assert the zeta explicit formula, a zero-count estimate, the actual
critical strip, a published zero-free region, or finite verified criticality.
Those analytic providers remain separate obligations for the application.

Source: direct Gaussian factorization, accompanying
`GaussianSignedMatricesResearch20261029.md`.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.GaussianLocalization

/-- Split one Gaussian factor off before extracting the uniform exponential
rate. This retains a summable dominating sequence independent of `R`. -/
theorem weighted_exp_factor_bound (w θ η R : ℝ)
    (hw : 0 ≤ w) (hθ : θ ≤ η) (hR : 1 ≤ R) :
    w * Real.exp (θ * R) ≤
      Real.exp (η * (R - 1)) * (w * Real.exp θ) := by
  have hmul : θ * (R - 1) ≤ η * (R - 1) :=
    mul_le_mul_of_nonneg_right hθ (sub_nonneg.mpr hR)
  calc
    w * Real.exp (θ * R) =
        (w * Real.exp θ) * Real.exp (θ * (R - 1)) := by
      rw [show θ * R = θ + θ * (R - 1) by ring, Real.exp_add]
      ring
    _ ≤ (w * Real.exp θ) * Real.exp (η * (R - 1)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hmul)
        (mul_nonneg hw (Real.exp_pos _).le)
    _ = _ := mul_comm _ _

/-- The complete signed or complex series has the extracted exponential rate.
No positivity of the summands is assumed. -/
theorem norm_tsum_le_exp_rate {ι E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (f : ι → E) (w θ : ι → ℝ) (η R : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hθ : ∀ i, θ i ≤ η) (hR : 1 ≤ R)
    (hs : Summable (fun i => w i * Real.exp (θ i)))
    (hf : ∀ i, ‖f i‖ ≤ w i * Real.exp (θ i * R)) :
    ‖∑' i, f i‖ ≤
      Real.exp (η * (R - 1)) * ∑' i, w i * Real.exp (θ i) := by
  let C := Real.exp (η * (R - 1))
  have hdom : ∀ i, ‖f i‖ ≤ C * (w i * Real.exp (θ i)) := by
    intro i
    exact (hf i).trans (weighted_exp_factor_bound (w i) (θ i) η R
      (hw i) (hθ i) hR)
  have hsum : Summable (fun i => C * (w i * Real.exp (θ i))) := hs.mul_left C
  have hn : Summable (fun i => ‖f i‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg (f i)) hdom hsum
  calc
    ‖∑' i, f i‖ ≤ ∑' i, ‖f i‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' i, C * (w i * Real.exp (θ i)) := Summable.tsum_le_tsum hdom hn hsum
    _ = C * ∑' i, w i * Real.exp (θ i) := by rw [tsum_mul_left]
    _ = _ := rfl

/-- Preserve a nonnegative local contribution and bound only the remote tail.
Taking `η = -(L^2-1/4)` gives exponential decay after local criticality has
been provided independently. -/
theorem nonnegative_head_add_tsum_lower {ι : Type*}
    (head : ℝ) (f : ι → ℝ) (w θ : ι → ℝ) (η R : ℝ)
    (hhead : 0 ≤ head) (hw : ∀ i, 0 ≤ w i)
    (hθ : ∀ i, θ i ≤ η) (hR : 1 ≤ R)
    (hs : Summable (fun i => w i * Real.exp (θ i)))
    (hf : ∀ i, |f i| ≤ w i * Real.exp (θ i * R)) :
    -(Real.exp (η * (R - 1)) * ∑' i, w i * Real.exp (θ i)) ≤
      head + ∑' i, f i := by
  have h := norm_tsum_le_exp_rate f w θ η R hw hθ hR hs
    (fun i => by simpa only [Real.norm_eq_abs] using hf i)
  rw [Real.norm_eq_abs] at h
  have hl := (abs_le.mp h).1
  linarith

/-- The tail exponent from a horizontal half-strip and an ordinate gap. -/
theorem gaussian_gap_exponent (δ x L : ℝ)
    (hδ : δ ^ 2 ≤ (1 : ℝ) / 4) (hx : L ^ 2 ≤ x ^ 2) :
    δ ^ 2 - x ^ 2 ≤ -(L ^ 2 - 1 / 4) := by
  linarith

/-- A positive local gap gives a rate strictly below the absolute exponent. -/
theorem exponent_below_quarter (b : ℝ) (hb0 : 0 ≤ b) (hb : b < 1 / 2) :
    b ^ 2 < (1 : ℝ) / 4 := by
  nlinarith

end RiemannResearch.Analysis.GaussianLocalization
