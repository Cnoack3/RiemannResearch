import RiemannResearch.Analysis.BroadKernelWeightedApproximation

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-! # Uniform weighted convergence survives an actual nonzero normalization limit -/

open MeasureTheory Set Filter
open scoped Topology
namespace RiemannResearch.Analysis

theorem weighted_quotient_error_le (A f w : ℝ → ℝ) (N N0 m E M : ℝ)
    (hN : 0 < N) (hw : ∀ x, 0 ≤ w x)
    (hA : ∀ x, w x * |A x - m*f x| ≤ E)
    (hf : ∀ x, w x * |f x| ≤ M) (x : ℝ) :
    w x * |A x/N - (m/N0)*f x| ≤
      E/N + |m| *M* |N⁻¹-N0⁻¹| := by
  have he : A x/N-(m/N0)*f x =
      (A x-m*f x)/N + m*f x*(N⁻¹-N0⁻¹) := by ring
  rw [he]
  calc
    _ ≤ w x*(|(A x-m*f x)/N| + |m*f x*(N⁻¹-N0⁻¹)|) :=
      mul_le_mul_of_nonneg_left (abs_add_le _ _) (hw x)
    _ = (w x* |A x-m*f x|)/N +
        |m| *(w x* |f x|)* |N⁻¹-N0⁻¹| := by
      rw [abs_div, abs_of_pos hN, abs_mul, abs_mul]
      ring
    _ ≤ E/N+ |m| *M* |N⁻¹-N0⁻¹| := add_le_add
      (div_le_div_of_nonneg_right (hA x) hN.le)
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hf x) (abs_nonneg m)) (abs_nonneg _))

theorem eventually_weighted_quotient_error_lt
    (A : ℝ → ℝ → ℝ) (N f w : ℝ → ℝ) (N0 m E M : ℝ)
    (hN0 : 0 < N0) (hN : Tendsto N atTop (𝓝 N0)) (hw : ∀ x, 0 ≤ w x)
    (hA : ∀ R : ℝ, 1 ≤ R → ∀ x, w x* |A R x-m*f x| ≤ E/R)
    (hf : ∀ x, w x* |f x| ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop, ∀ x,
      w x * |A R x/N R - (m/N0)*f x| < ε := by
  have hE0 : 0 ≤ E := by
    have he := hA 1 le_rfl 0
    simp only [div_one] at he
    exact (mul_nonneg (hw 0) (abs_nonneg _)).trans he
  have hNevent : ∀ᶠ R : ℝ in atTop, N0/2 ≤ N R :=
    (hN.eventually (Ioi_mem_nhds (show N0/2 < N0 by linarith))).mono
      (fun _ h => h.le)
  have hlimE : Tendsto (fun R : ℝ => (E/R)/(N0/2)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, zero_mul] using
      (tendsto_inv_atTop_zero.const_mul E).mul_const (N0/2)⁻¹
  have hconst : Tendsto (fun _ : ℝ => N0⁻¹) atTop (𝓝 N0⁻¹) := tendsto_const_nhds
  have hlimN : Tendsto (fun R => |(N R)⁻¹-N0⁻¹|) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero] using
      ((hN.inv₀ hN0.ne').sub hconst).abs
  have hlim : Tendsto (fun R : ℝ => (E/R)/(N0/2)+ |m| *M* |(N R)⁻¹-N0⁻¹|)
      atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using hlimE.add (hlimN.const_mul (|m| *M))
  filter_upwards [hNevent, eventually_ge_atTop (1 : ℝ), hlim.eventually_lt_const hε]
    with R hNR hR hbound
  intro x
  have hR0 : 0 < R := by linarith
  have hNR0 : 0 < N R := lt_of_lt_of_le (by linarith : 0 < N0/2) hNR
  exact (weighted_quotient_error_le (A R) f w (N R) N0 m (E/R) M hNR0 hw
    (hA R hR) hf x).trans_lt ((add_le_add
      (div_le_div_of_nonneg_left (div_nonneg hE0 hR0.le) (by linarith : 0<N0/2) hNR)
      le_rfl).trans_lt hbound)

end RiemannResearch.Analysis
