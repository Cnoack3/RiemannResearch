import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact summation of power masses over unit cells

Source: elementary integration and telescoping used in the user's Mellin
mode energy estimates. The positive cell integrals have an actual `HasSum`,
not merely a value assigned to a possibly divergent series.
-/

noncomputable section
set_option autoImplicit false
open Filter MeasureTheory
open scoped Topology BigOperators Interval

namespace RiemannResearch.RH.Pareto.SpectralObstruction

def powerCellMass (β a : ℝ) (n : ℕ) : ℝ :=
  ∫ x in (n : ℝ) + a..(n : ℝ) + a + 1, x ^ (-2 * β)

theorem powerCellMass_nonneg (β a : ℝ) (ha : 0 < a) (n : ℕ) :
    0 ≤ powerCellMass β a n := by
  apply intervalIntegral.integral_nonneg (by linarith)
  intro x hx
  exact Real.rpow_nonneg ((show 0 ≤ (n : ℝ) + a by positivity).trans hx.1) _

theorem powerCellMass_eq (β a : ℝ) (hβ : (1 / 2 : ℝ) < β)
    (ha : 0 < a) (n : ℕ) :
    powerCellMass β a n =
      (((n : ℝ) + a) ^ (1 - 2 * β) -
        ((n : ℝ) + a + 1) ^ (1 - 2 * β)) / (2 * β - 1) := by
  have hzero : (0 : ℝ) ∉ Set.uIcc ((n : ℝ) + a) ((n : ℝ) + a + 1) := by
    rw [Set.uIcc_of_le (by linarith)]
    intro hz
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith [hz.1]
  rw [powerCellMass, integral_rpow (Or.inr ⟨by linarith, hzero⟩)]
  rw [show -2 * β + 1 = 1 - 2 * β by ring]
  have hd : 1 - 2 * β = -(2 * β - 1) := by ring
  have hdiv (x y : ℝ) : (x - y) / (1 - 2 * β) = (y - x) / (2 * β - 1) := by
    rw [hd, div_neg]
    ring
  exact hdiv _ _

theorem powerCellMass_sum_range (β a : ℝ) (hβ : (1 / 2 : ℝ) < β)
    (ha : 0 < a) (N : ℕ) :
    (∑ n ∈ Finset.range N, powerCellMass β a n) =
      (a ^ (1 - 2 * β) - ((N : ℝ) + a) ^ (1 - 2 * β)) / (2 * β - 1) := by
  induction N with
  | zero => simp
  | succ N hN =>
      rw [Finset.sum_range_succ, hN, powerCellMass_eq β a hβ ha N]
      push_cast
      rw [show (N : ℝ) + 1 + a = (N : ℝ) + a + 1 by ring]
      ring

/-- Positive unit-cell masses sum to the exact power-tail integral. -/
theorem powerCellMass_hasSum (β a : ℝ) (hβ : (1 / 2 : ℝ) < β)
    (ha : 0 < a) :
    HasSum (powerCellMass β a) (a ^ (1 - 2 * β) / (2 * β - 1)) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (powerCellMass_nonneg β a ha) _).2
  have hx : Tendsto (fun N : ℕ => (N : ℝ) + a) atTop atTop :=
    tendsto_atTop_add_const_right atTop a tendsto_natCast_atTop_atTop
  have hp : Tendsto (fun N : ℕ => ((N : ℝ) + a) ^ (1 - 2 * β))
      atTop (𝓝 0) := by
    have hh := (tendsto_rpow_neg_atTop (show 0 < 2 * β - 1 by linarith)).comp hx
    simpa only [Function.comp_def, show -(2 * β - 1) = 1 - 2 * β by ring] using hh
  have hh := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => a ^ (1 - 2 * β))
    atTop (𝓝 (a ^ (1 - 2 * β)))).sub hp).div_const (2 * β - 1)
  simpa only [powerCellMass_sum_range β a hβ ha, sub_zero] using hh

theorem powerCellMass_summable (β a : ℝ) (hβ : (1 / 2 : ℝ) < β)
    (ha : 0 < a) : Summable (powerCellMass β a) :=
  (powerCellMass_hasSum β a hβ ha).summable

theorem powerCellMass_tsum (β a : ℝ) (hβ : (1 / 2 : ℝ) < β)
    (ha : 0 < a) :
    (∑' n : ℕ, powerCellMass β a n) = a ^ (1 - 2 * β) / (2 * β - 1) :=
  (powerCellMass_hasSum β a hβ ha).tsum_eq

end RiemannResearch.RH.Pareto.SpectralObstruction
