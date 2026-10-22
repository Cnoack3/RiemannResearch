import RiemannResearch.Analysis.BoundedPrimitiveAbel
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Pairing limits with a summably dominated primitive

Source: the Abel argument in
`RH/ReciprocalCharge_DilationAndPeriodicSource_20260924.md`, Section 7,
extended here from bounded primitives to primitives integrable against the
variation majorant. Ordinary summability and the endpoint condition remain
explicit. No boundedness of the primitive is assumed.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.Analysis

/-- Dominated variation permits an unbounded primitive whenever its absolute
    value is summable against the variation majorant. -/
theorem dominatedPrimitive_pairing_tendsto_zero
    (h H : ℕ → ℝ) (F : ℕ → ℕ → ℝ) (D : ℕ → ℝ)
    (hzero : H 0 = 0) (hstep : ∀ k, H (k + 1) = H k + h k)
    (hboundary : ∀ᶠ N in atTop,
      Tendsto (fun k => H k * F N k) atTop (𝓝 0))
    (hs : ∀ N, Summable (fun k => h k * F N k))
    (hD : Summable (fun k => |H (k + 1)| * D k))
    (hv : ∀ᶠ N in atTop, ∀ k, |F N k - F N (k + 1)| ≤ D k)
    (hp : ∀ k, Tendsto (fun N => F N k) atTop (𝓝 0)) :
    Tendsto (fun N => ∑' k, h k * F N k) atTop (𝓝 0) := by
  have hdom : ∀ᶠ N in atTop, ∀ k,
      ‖H (k + 1) * (F N k - F N (k + 1))‖ ≤ |H (k + 1)| * D k := by
    filter_upwards [hv] with N hN
    intro k
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hN k) (abs_nonneg _)
  have hpt : ∀ k, Tendsto
      (fun N => H (k + 1) * (F N k - F N (k + 1))) atTop (𝓝 0) := by
    intro k
    simpa only [sub_self, mul_zero] using
      ((hp k).sub (hp (k + 1))).const_mul (H (k + 1))
  have ht := tendsto_tsum_of_dominated_convergence hD hpt hdom
  simp only [tsum_zero] at ht
  apply ht.congr'
  filter_upwards [hdom, hboundary] with N hN hend
  have hsum : Summable (fun k => H (k + 1) * (F N k - F N (k + 1))) :=
    Summable.of_norm_bounded hD hN
  have hleft : Summable (fun k => (H (k + 1) - H k) * F N k) := by
    simpa only [hstep, add_sub_cancel_left] using hs N
  have hdiff (k : ℕ) : H (k + 1) - H k = h k := by
    rw [hstep]
    ring
  have he := boundedPrimitive_abel_tsum H (F N) hleft hsum hend
  simp only [hdiff, hzero, neg_zero, zero_mul, zero_add] at he
  exact he.symm

end RiemannResearch.Analysis
