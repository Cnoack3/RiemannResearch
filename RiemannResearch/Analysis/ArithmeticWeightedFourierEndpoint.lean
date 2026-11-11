/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ArithmeticWeightedFourierRemainder
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp

/-!
# Endpoint and uniform Fourier synthesis

Source: Sections 6--7 of `FRZ_Strengthening_2026-11-10.pdf`.
Dominated mode convergence gives fixed weighted Wiener convergence. A stronger
weight gives uniform convergence on its unit ball as soon as the quotient of
the original and stronger weights tends to zero off finite sets. This precise
tail condition covers logarithmic as well as positive-power improvements.
The arithmetic mode estimates are supplied in ActualRationalHorizontalEndpoint.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.Fourier

/-- Tannery with the Fourier coefficients and arithmetic weight exposed. -/
theorem tendsto_weightedFourierPairing_zero {ι τ : Type*} {l : Filter τ}
    (c : ι → ℂ) (e : τ → ι → ℂ) (w : ι → ℝ) (C : ℝ)
    (hc : Summable (fun i => ‖c i‖ * w i))
    (hpt : ∀ i, Tendsto (fun t => e t i) l (𝓝 0))
    (hb : ∀ᶠ t in l, ∀ i, ‖e t i‖ ≤ C * w i) :
    Tendsto (fun t => weightedFourierPairing c (e t)) l (𝓝 0) := by
  have hpt' : ∀ i, Tendsto (fun t => c i * e t i) l (𝓝 0) := by
    intro i
    simpa only [mul_zero] using (hpt i).const_mul (c i)
  have hdom : ∀ᶠ t in l, ∀ i, ‖c i * e t i‖ ≤ C * (‖c i‖ * w i) := by
    filter_upwards [hb] with t ht
    intro i
    rw [norm_mul]
    calc
      _ ≤ ‖c i‖ * (C * w i) := mul_le_mul_of_nonneg_left (ht i) (norm_nonneg _)
      _ = _ := by ring
  simpa only [weightedFourierPairing, tsum_zero] using
    tendsto_tsum_of_dominated_convergence (hc.mul_left C) hpt' hdom

/-- The min envelope retains both endpoint bounds rather than selecting a
single regularity class in advance. -/
theorem norm_le_saturated_of_two_bounds (z : ℂ) (C w L : ℝ)
    (hC : 0 ≤ C) (hL : 0 < L)
    (h₂ : ‖z‖ ≤ C * w ^ 2 / L) (h₄ : ‖z‖ ≤ C * w ^ 4 / L ^ 3) :
    ‖z‖ ≤ (C * w ^ 2 / L) * min 1 (w ^ 2 / L ^ 2) := by
  have hbase : 0 ≤ C * w ^ 2 / L := by positivity
  rw [mul_min_of_nonneg _ _ hbase, mul_one]
  apply le_min h₂
  calc
    ‖z‖ ≤ C * w ^ 4 / L ^ 3 := h₄
    _ = (C * w ^ 2 / L) * (w ^ 2 / L ^ 2) := by ring

/-- The elementary real-exponent interpolation underlying every 2<s≤4
Wiener bound. It also includes both endpoints. -/
theorem min_one_sq_le_rpow (x δ : ℝ) (hx : 0 ≤ x)
    (hδ : 0 ≤ δ) (hδ₂ : δ ≤ 2) :
    min 1 (x ^ 2) ≤ x ^ δ := by
  by_cases hx0 : x = 0
  · subst x
    simp only [zero_pow (by norm_num : 2 ≠ 0), min_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
    exact Real.rpow_nonneg (by norm_num) δ
  have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  by_cases hx1 : x ≤ 1
  · calc
      _ ≤ x ^ 2 := min_le_right _ _
      _ = x ^ (2 : ℝ) := (Real.rpow_natCast x 2).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hxp hx1 hδ₂
  · calc
      _ ≤ 1 := min_le_left _ _
      _ = x ^ (0 : ℝ) := (Real.rpow_zero x).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) hδ

/-- Finite-coordinate convergence and a tight stronger-weight tail imply a
uniform mode estimate. The tail assumption is an explicit condition on the
weights alone, not on the Fourier remainder being proved small. -/
theorem eventually_uniform_mode_bound_of_tight_weight {ι τ : Type*} {l : Filter τ}
    (e : τ → ι → ℂ) (w v : ι → ℝ) (C : ℝ)
    (hC : 0 < C) (hv : ∀ i, 0 < v i)
    (hpt : ∀ i, Tendsto (fun t => e t i) l (𝓝 0))
    (hb : ∀ᶠ t in l, ∀ i, ‖e t i‖ ≤ C * w i)
    (htail : ∀ η : ℝ, 0 < η → ∃ F : Finset ι, ∀ i ∉ F, w i ≤ η * v i)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t in l, ∀ i, ‖e t i‖ ≤ ε * v i := by
  classical
  obtain ⟨F, hF⟩ := htail (ε / C) (div_pos hε hC)
  have hfin : ∀ᶠ t in l, ∀ i ∈ F, ‖e t i‖ ≤ ε * v i := by
    apply (Filter.eventually_all_finset F).2
    intro i hi
    have hh : Tendsto (fun t => ‖e t i‖) l (𝓝 0) := by simpa using (hpt i).norm
    exact hh.eventually_le_const (mul_pos hε (hv i))
  filter_upwards [hb, hfin] with t hbound hfinite
  intro i
  by_cases hi : i ∈ F
  · exact hfinite i hi
  · calc
      _ ≤ C * w i := hbound i
      _ ≤ C * ((ε / C) * v i) := mul_le_mul_of_nonneg_left (hF i hi) hC.le
      _ = _ := by field_simp

/-- Uniform convergence on the unit ball of any strictly stronger Wiener
weight satisfying the finite-tail criterion. This is stronger than restricting
the improvement to weights w^(2+ε). -/
theorem eventually_uniform_weightedFourier_unitBall {ι τ : Type*} {l : Filter τ}
    (e : τ → ι → ℂ) (w v : ι → ℝ) (C : ℝ)
    (hC : 0 < C) (hv : ∀ i, 0 < v i)
    (hpt : ∀ i, Tendsto (fun t => e t i) l (𝓝 0))
    (hb : ∀ᶠ t in l, ∀ i, ‖e t i‖ ≤ C * w i)
    (htail : ∀ η : ℝ, 0 < η → ∃ F : Finset ι, ∀ i ∉ F, w i ≤ η * v i)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t in l, ∀ c : ι → ℂ,
      Summable (fun i => ‖c i‖ * v i) → weightedFourierMass c v ≤ 1 →
      ‖weightedFourierPairing c (e t)‖ ≤ ε := by
  filter_upwards [eventually_uniform_mode_bound_of_tight_weight e w v C hC hv
    hpt hb htail ε hε] with t ht
  intro c hc hmass
  have hmode : ∀ i, ‖e t i‖ ≤ (ε / 1) * v i := by simpa using ht
  have h := weightedFourierRemainder_norm_le c (e t) v ε 1 hc hmode
  change ‖weightedFourierPairing c (e t)‖ ≤ _ at h
  simp only [div_one] at h
  exact h.trans (by nlinarith)

end RiemannResearch.Fourier
