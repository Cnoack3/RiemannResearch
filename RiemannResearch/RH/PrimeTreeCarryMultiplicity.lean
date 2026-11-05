/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.RH.PrimeTreeCarryFactorization
import Mathlib.Analysis.Analytic.Order
import Mathlib.Tactic

/-! # Multiplicities in the joint carry detector
Source: C. Noack, *Prime trees, fractional parts, and zeta zeros* (2026),
§5.1. Zero order is stable under multiplication by the local holomorphic unit
1/s, and the two explicit carry multipliers have no common zero in the strip.
-/

noncomputable section
open Filter Set
open scoped BigOperators Topology
namespace RiemannResearch.RH.CanonicalPrimeCarry
open PrimeTreeTwoCarry

/-- Exact cancellation in the entire multipliers for first lifts one and three. -/
theorem first_third_multiplier_difference (s : ℂ) :
    3 * carryMultiplier 1 s - carryMultiplier 0 s = 2 * periodicFactor s := by
  have htail (k : ℕ) : primeMomentTerm 1 (k+1) s = (1/3 : ℂ) * primeMomentTerm 0 (k+1) s := by
    simp [primeMomentTerm, oddChain_edgeMass_succ, liftU]
    ring
  have h0 : primeMomentTerm 0 0 s = (2/3 : ℂ) * (3 : ℂ)^(1-s) := by
    simp [primeMomentTerm, oddChain_edgeMass_zero, liftU, radix, primeAt]
    ring
  have h3 : primeMomentTerm 1 0 s = (8/9 : ℂ) * (3 : ℂ)^(1-s) := by
    simp [primeMomentTerm, oddChain_edgeMass_zero, liftU, radix, primeAt]
    ring
  have he : (3 : ℂ)^(1-s) = 3 * (3 : ℂ)^(-s) := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ (by norm_num : (3 : ℂ) ≠ 0), Complex.cpow_one]
  unfold carryMultiplier periodicFactor
  rw [(momentSeries_summable 1 s).tsum_eq_zero_add, (momentSeries_summable 0 s).tsum_eq_zero_add, h0, h3, he]
  simp_rw [htail]
  rw [tsum_mul_left]
  ring

theorem first_third_multipliers_disjoint (s : ℂ) (hs : s.re < 1) :
    carryMultiplier 0 s ≠ 0 ∨ carryMultiplier 1 s ≠ 0 := by
  by_cases h0 : carryMultiplier 0 s = 0
  · right
    intro h3
    have h := first_third_multiplier_difference s
    rw [h0, h3] at h
    exact periodicFactor_ne_zero s hs (by linear_combination - (1/2 : ℂ) * h)
  · exact Or.inl h0

theorem carry_readout_order (j : ℕ) (s : ℂ) (hs : 0 < s.re) (hlt : s.re < 1) :
    analyticOrderAt (readout (oddChain j).chainSignal) s =
      analyticOrderAt riemannZeta s + analyticOrderAt (carryMultiplier j) s := by
  let u : ℂ → ℂ := fun z => z⁻¹
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have hs1 : s ≠ 1 := by rintro rfl; norm_num at hlt
  have hz : AnalyticAt ℂ riemannZeta s := by
    apply DifferentiableOn.analyticAt (s := ({1}ᶜ : Set ℂ)) _
      (isOpen_compl_singleton.mem_nhds hs1)
    exact fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt
  have hu : AnalyticAt ℂ u s := analyticAt_id.inv hs0
  have hb := (carryMultiplier_entire j).analyticAt s
  have hnear : ∀ᶠ z : ℂ in 𝓝 s, 0 < z.re ∧ z.re < 1 :=
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds ⟨hs, hlt⟩
  have he : readout (oddChain j).chainSignal =ᶠ[𝓝 s] riemannZeta * (u * carryMultiplier j) := by
    filter_upwards [hnear] with z hz
    have hr : z ≠ 1 := by rintro rfl; simpa using hz.2
    rw [carry_readout_zeta _ _ hz.1 hr]
    simp only [Pi.mul_apply, u, div_eq_mul_inv]
    ring
  rw [analyticOrderAt_congr he, analyticOrderAt_mul hz (hu.mul hb),
    analyticOrderAt_mul hu hb, analyticOrderAt_eq_zero.mpr (Or.inr (inv_ne_zero hs0)), zero_add]

/-- The smaller order of the two physical Mellin integrals is the zeta order.
No zero, simplicity, or RH hypothesis is required. -/
theorem min_carry_readout_orders (s : ℂ) (hs : 0 < s.re) (hlt : s.re < 1) :
    min (analyticOrderAt (readout (oddChain 0).chainSignal) s)
        (analyticOrderAt (readout (oddChain 1).chainSignal) s) =
      analyticOrderAt riemannZeta s := by
  rw [carry_readout_order 0 s hs hlt, carry_readout_order 1 s hs hlt]
  rcases first_third_multipliers_disjoint s hlt with h | h
  · rw [analyticOrderAt_eq_zero.mpr (Or.inr h), add_zero, min_eq_left]
    exact le_add_of_nonneg_right zero_le
  · rw [analyticOrderAt_eq_zero.mpr (Or.inr h), add_zero, min_eq_right]
    exact le_add_of_nonneg_right zero_le

end RiemannResearch.RH.CanonicalPrimeCarry
