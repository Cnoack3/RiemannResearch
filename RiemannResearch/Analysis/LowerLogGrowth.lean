/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.SubpolynomialCofinalGrowth
import RiemannResearch.Analysis.NonnegativeDeficit
import Mathlib.Data.ENNReal.Real

/-!
# Normalized Cesàro energy and lower logarithmic growth

Source: user-provided
`Conditional_IID_Pareto_Cesaro_Research_Agenda_2026-11-01.md`,
Sections 8 and 11.5. This formalizes the stated sufficient condition;
it does not construct a family meeting its arithmetic growth premise.
-/

noncomputable section
open Filter
open scoped Topology ENNReal
namespace RiemannResearch.Analysis.SubpolynomialWindow

/-- Extended nonnegative liminf: divergent growth is not assigned the default
real infimum. For nonnegative energies and cofinal heads this is the usual
extended lower logarithmic growth exponent. -/
def lowerLogGrowth (E H : ℕ → ℝ) : ℝ≥0∞ :=
  Filter.liminf (fun j => ENNReal.ofReal
    (Real.log (1 + E j) / Real.log (H j))) atTop

theorem lowerLogGrowth_eq_zero_iff (E H : ℕ → ℝ) :
    lowerLogGrowth E H = 0 ↔
      ∀ ε : ℝ, 0 < ε → ∃ᶠ j in atTop,
        Real.log (1 + E j) / Real.log (H j) < ε := by
  rw [lowerLogGrowth, NonnegativeDeficit.liminf_eq_zero_iff_cofinallySmall]
  constructor
  · intro h ε hε
    apply Filter.frequently_atTop.2
    intro N
    obtain ⟨j, hjN, hj⟩ := h (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε) N
    exact ⟨j, hjN, (ENNReal.ofReal_lt_ofReal_iff hε).mp hj⟩
  · intro h ε hε N
    by_cases ht : ε = ⊤
    · exact ⟨N, le_rfl, by simp [ht]⟩
    have hp : 0 < ε.toReal := ENNReal.toReal_pos (ne_of_gt hε) ht
    obtain ⟨j, hjN, hj⟩ := Filter.frequently_atTop.mp (h ε.toReal hp) N
    refine ⟨j, hjN, ?_⟩
    rw [← ENNReal.ofReal_toReal ht]
    exact (ENNReal.ofReal_lt_ofReal_iff hp).mpr hj

theorem no_positive_power_floor_of_lowerLogGrowth_zero
    (x E : ℕ → ℝ) (K c a : ℝ)
    (hx : Tendsto x atTop atTop)
    (hE : ∀ n, 0 ≤ E n) (hK : 1 ≤ K) (hc : 0 < c) (ha : 0 < a)
    (hsmall : lowerLogGrowth E x = 0)
    (hfloor : ∀ᶠ n in atTop, c * (x n) ^ a ≤ E n + K) : False :=
  no_positive_power_floor_of_frequently_small_relativeLog x E K c a
    hx hE hK hc ha ((lowerLogGrowth_eq_zero_iff E x).mp hsmall) hfloor

end RiemannResearch.Analysis.SubpolynomialWindow
