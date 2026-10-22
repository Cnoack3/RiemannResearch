import RiemannResearch.RH.NymanBroadSchwartzConvergence
import RiemannResearch.RH.NymanBroadKernelEnergy
import RiemannResearch.Analysis.SuperexponentialSchwartz

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# The actual broad arithmetic family converges in Mathlib's Schwartz topology

The harmless scale clamp max(1,R) makes the family defined at every real R;
it is exactly the requested actual family for every R≥1. Membership is
proved from actual all-derivative superexponential decay, and convergence
uses Mathlib's actual seminorm topology.
-/

open MeasureTheory Set Filter
open scoped Topology SchwartzMap
namespace RiemannResearch.RH
open RiemannResearch.Analysis

noncomputable def nymanBroadSchwartzMap (n : ℕ) (hn : 0 < n)
    {φ : ℝ → ℝ} {a b : ℝ} (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (ha : ∀ x < a, φ x = 0) (hb : ∀ x > b, φ x = 0) (R : ℝ) : SchwartzMap ℝ ℝ :=
  schwartzMapOfSmoothSuperexponential (nymanBroadProfile n φ (max 1 R))
    (contDiff_nymanBroadProfile n hn hφ ha hb (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))
    (superexponential_iteratedDeriv_nymanBroadProfile n hn hφ ha hb
      (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))

theorem nymanBroadSchwartzMap_apply_of_one_le (n : ℕ) (hn : 0 < n)
    {φ : ℝ → ℝ} {a b R : ℝ} (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (ha : ∀ x < a, φ x = 0) (hb : ∀ x > b, φ x = 0) (hR : 1 ≤ R) (x : ℝ) :
    nymanBroadSchwartzMap n hn hφ ha hb R x = nymanBroadProfile n φ R x := by
  change nymanBroadProfile n φ (max 1 R) x = _
  rw [max_eq_right hR]

theorem tendsto_nymanBroadSchwartzMap (n : ℕ) (hn : 2 ≤ n)
    {φ : ℝ → ℝ} {a b : ℝ} (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (ha : ∀ x < a, φ x = 0) (hb : ∀ x > b, φ x = 0)
    (hmass : (∫ x, φ x) ≠ 0) :
    Tendsto (nymanBroadSchwartzMap n (by omega) hφ ha hb) atTop
      (𝓝 (nymanBroadLimitScale n φ •
        (broadProfile_hasCompactSupport_of_bounds ha hb).toSchwartzMap hφ)) := by
  apply tendsto_schwartzMap_of_weighted_iteratedDeriv
  intro k j ε hε
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_weighted_iteratedDeriv_nymanBroadProfile_error_lt n hn hφ
      (broadProfile_hasCompactSupport_of_bounds ha hb) hmass k j ε hε] with R hR hc
  intro x
  change polynomialWeight k x * ‖iteratedDeriv j (nymanBroadProfile n φ (max 1 R)) x -
    iteratedDeriv j (fun y => nymanBroadLimitScale n φ * φ y) x‖ < ε
  rw [max_eq_right hR, iteratedDeriv_const_mul_field, Real.norm_eq_abs]
  exact hc x

end RiemannResearch.RH
