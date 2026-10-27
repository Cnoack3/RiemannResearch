/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ArithmeticCumulativeBasic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A large prime-two increment at the midpoint of an odd conductor

Source: the paper argument LegalSubspaceProjectionObstruction.md supplied in
this research continuation. These deterministic statements require the
decomposition and coefficient estimates explicitly; they do not provide the
Hilbert-space estimates for the actual projected correction.
-/

noncomputable section
open Filter
namespace RiemannResearch.RH.ResidueMidpointIncrement
open ArithmeticCumulative

/-- Exact residue jump across the midpoint of an odd conductor. -/
theorem residueFraction_double_midpoint (d : ℕ) (hd : 3 ≤ d)
    (hodd : d % 2 = 1) :
    residueFraction d (2 * ((d + 1) / 2)) -
      residueFraction d ((d + 1) / 2) =
        -((d : ℝ) - 1) / (2 * (d : ℝ)) := by
  have hn : (d + 1) / 2 < d := by omega
  have hdouble : 2 * ((d + 1) / 2) = d + 1 := by omega
  have hmod : (2 * ((d + 1) / 2)) % d = 1 := by
    rw [hdouble]
    simp [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < d by omega)]
  have hcast : 2 * (((d + 1) / 2 : ℕ) : ℝ) = (d : ℝ) + 1 := by
    exact_mod_cast hdouble
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  unfold residueFraction
  rw [hmod, Nat.mod_eq_of_lt hn]
  push_cast
  field_simp [hd0]
  nlinarith only [hcast]

/-- A nonnegative residue amplitude and uniformly bounded remainder force a
large physical increment. The exact midpoint jump is retained above. -/
theorem increment_lower_of_decomposition (d : ℕ) (hd : 3 ≤ d)
    (hodd : d % 2 = 1) (b w : ℕ → ℝ) (c C : ℝ) (hc : 0 ≤ c)
    (hb : ∀ n, b n = c * residueFraction d n + w n)
    (hw : ∀ n, |w n| ≤ C) :
    c / 4 - 2 * C ≤ |b (2 * ((d + 1) / 2)) - b ((d + 1) / 2)| := by
  let n := (d + 1) / 2
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hratio : (1 : ℝ) / 4 ≤ ((d : ℝ) - 1) / (2 * (d : ℝ)) := by
    apply (le_div_iff₀ (show 0 < 2 * (d : ℝ) by positivity)).mpr
    nlinarith only [hdR]
  have hdiff : b (2 * n) - b n =
      -c * (((d : ℝ) - 1) / (2 * (d : ℝ))) + w (2 * n) - w n := by
    calc
      _ = c * (residueFraction d (2 * n) - residueFraction d n) +
          w (2 * n) - w n := by rw [hb, hb]; ring
      _ = _ := by
        rw [residueFraction_double_midpoint d hd hodd]
        ring
  have hneg := neg_le_abs (b (2 * n) - b n)
  have hwup : w (2 * n) ≤ C := (abs_le.mp (hw (2 * n))).2
  have hwlo : -C ≤ w n := (abs_le.mp (hw n)).1
  have hprod := mul_le_mul_of_nonneg_left hratio hc
  change c / 4 - 2 * C ≤ |b (2 * n) - b n|
  nlinarith only [hdiff, hneg, hwup, hwlo, hprod]

/-- Specialization to the high-conductor amplitude in the legal-subspace
obstruction. The lower coefficient and remainder bounds remain premises. -/
theorem increment_lower_of_sqrt_decomposition (d : ℕ) (hd : 3 ≤ d)
    (hodd : d % 2 = 1) (b w : ℕ → ℝ) (β β₀ C : ℝ)
    (hβ₀ : 0 ≤ β₀) (hβ : β₀ ≤ β)
    (hb : ∀ n, b n = β * 10 * Real.sqrt (d : ℝ) * residueFraction d n + w n)
    (hw : ∀ n, |w n| ≤ C) :
    (β₀ * 10 / 4) * Real.sqrt (d : ℝ) - 2 * C ≤
      |b (2 * ((d + 1) / 2)) - b ((d + 1) / 2)| := by
  have hβpos : 0 ≤ β := hβ₀.trans hβ
  have hlo := increment_lower_of_decomposition d hd hodd b w
    (β * 10 * Real.sqrt (d : ℝ)) C (by positivity) hb hw
  have hprod := mul_le_mul_of_nonneg_right hβ (Real.sqrt_nonneg (d : ℝ))
  nlinarith only [hlo, hprod]

/-- The deterministic lower bound diverges along any conductor sequence whose
square roots tend to infinity, provided the coefficient floor stays positive.
This may be applied to an increasing prime sequence after its arithmetic
decomposition estimates have been established. -/
theorem increment_tendsto_atTop_of_sqrt_lower
    (d : ℕ → ℕ) (b : ℕ → ℕ → ℝ) (β₀ C : ℝ) (hβ₀ : 0 < β₀)
    (hsqrt : Tendsto (fun i => Real.sqrt (d i : ℝ)) atTop atTop)
    (hlower : ∀ᶠ i : ℕ in atTop,
      (β₀ * 10 / 4) * Real.sqrt (d i : ℝ) - 2 * C ≤
        |b i (2 * ((d i + 1) / 2)) - b i ((d i + 1) / 2)|) :
    Tendsto (fun i => |b i (2 * ((d i + 1) / 2)) -
      b i ((d i + 1) / 2)|) atTop atTop := by
  apply tendsto_atTop.2
  intro M
  have hc : 0 < β₀ * 10 / 4 := by positivity
  filter_upwards [(tendsto_atTop.1 hsqrt) ((M + 2 * C) / (β₀ * 10 / 4)), hlower]
    with i hi hli
  have hm : M + 2 * C ≤ (β₀ * 10 / 4) * Real.sqrt (d i : ℝ) := by
    have hm' := (div_le_iff₀ hc).mp hi
    simpa only [mul_comm] using hm'
  linarith only [hm, hli]

end RiemannResearch.RH.ResidueMidpointIncrement
