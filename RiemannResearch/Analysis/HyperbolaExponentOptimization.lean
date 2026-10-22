/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

/-!
# Integer hyperbola cutoffs and sharp exponent feasibility

Pure real-variable estimates, independent of the arithmetic application.
Sharpness refers to the separate positive power/log majorants only.
-/

open Filter
open scoped Topology

namespace RiemannResearch.Analysis

/-- A conductor-uniform hyperbola estimate optimizes at the integer
cutoff `floor (N^(1/(p+r)))`. No arithmetic cancellation assumption is
hidden: the entire two-term bound is the explicit input `hE`. -/
theorem eventual_power_envelope_of_hyperbola_bound
    (E : ℕ → ℕ → ℝ) (p r A B : ℝ)
    (hp : (1 : ℝ) / 2 ≤ p) (hr : p < r)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hE : ∀ M N y : ℕ, 0 < y → y ≤ N →
      |E M N| ≤ A * (y : ℝ) ^ p + B * (N : ℝ) * (y : ℝ) ^ (-r)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ N : ℕ in atTop, ∀ M : ℕ,
      |E M N| ≤ K * (N : ℝ) ^ (p / (p + r)) := by
  have hp0 : 0 ≤ p := by linarith
  have hr0 : 0 < r := by linarith
  have hs : 0 < p + r := by linarith
  have hs1 : 1 ≤ p + r := by linarith
  let θ : ℝ := 1 / (p + r)
  let β : ℝ := p / (p + r)
  have hθ : 0 < θ := div_pos (by norm_num) hs
  have hθ1 : θ ≤ 1 := by
    dsimp [θ]
    apply (div_le_iff₀ hs).2
    simpa using hs1
  have hexp : θ * p = β := by dsimp [θ, β]; ring
  have hexptail : 1 + θ * (-r) = β := by
    dsimp [θ, β]
    field_simp [ne_of_gt hs]
    ring
  have hlim : Tendsto (fun N : ℕ => (N : ℝ) ^ θ) atTop atTop :=
    (tendsto_rpow_atTop hθ).comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ N ∧ 2 ≤ (N : ℝ) ^ θ := by
    filter_upwards [eventually_ge_atTop (1 : ℕ),
      hlim.eventually (eventually_ge_atTop (2 : ℝ))] with N hN hpow
    exact ⟨by exact_mod_cast hN, hpow⟩
  refine ⟨A + B * (2 : ℝ) ^ r, by positivity, ?_⟩
  filter_upwards [hevent] with N hN M
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (by norm_num) hN.1
  have hN0 : (0 : ℝ) ≤ N := hNpos.le
  have hpowpos : 0 < (N : ℝ) ^ θ := Real.rpow_pos_of_pos hNpos θ
  let y : ℕ := ⌊(N : ℝ) ^ θ⌋₊
  have hy : 0 < y := Nat.floor_pos.mpr (by linarith [hN.2])
  have hyN : y ≤ N :=
    Nat.floor_le_of_le (Real.rpow_le_self_of_one_le hN.1 hθ1)
  have hyupper : (y : ℝ) ≤ (N : ℝ) ^ θ := Nat.floor_le hpowpos.le
  have hyfloor : (N : ℝ) ^ θ < (y : ℝ) + 1 := Nat.lt_floor_add_one _
  have hylower : (N : ℝ) ^ θ / 2 ≤ (y : ℝ) := by linarith [hN.2]
  have hhead : (y : ℝ) ^ p ≤ (N : ℝ) ^ β := by
    calc
      _ ≤ ((N : ℝ) ^ θ) ^ p :=
        Real.rpow_le_rpow (by positivity) hyupper hp0
      _ = (N : ℝ) ^ (θ * p) := (Real.rpow_mul hN0 θ p).symm
      _ = _ := by rw [hexp]
  have htailbase : (y : ℝ) ^ (-r) ≤
      (2 : ℝ) ^ r * (N : ℝ) ^ (θ * (-r)) := by
    calc
      _ ≤ ((N : ℝ) ^ θ / 2) ^ (-r) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hylower (by linarith)
      _ = (2 : ℝ) ^ r * (N : ℝ) ^ (θ * (-r)) := by
        rw [Real.div_rpow hpowpos.le (by norm_num),
          ← Real.rpow_mul hN0 θ (-r), Real.rpow_neg (by norm_num) r]
        simp only [div_eq_mul_inv, inv_inv]
        ring
  have htail : (N : ℝ) * (y : ℝ) ^ (-r) ≤
      (2 : ℝ) ^ r * (N : ℝ) ^ β := by
    calc
      _ ≤ (N : ℝ) * ((2 : ℝ) ^ r * (N : ℝ) ^ (θ * (-r))) :=
        mul_le_mul_of_nonneg_left htailbase hN0
      _ = (2 : ℝ) ^ r * ((N : ℝ) ^ (1 : ℝ) *
          (N : ℝ) ^ (θ * (-r))) := by rw [Real.rpow_one]; ring
      _ = (2 : ℝ) ^ r * (N : ℝ) ^ (1 + θ * (-r)) := by
        rw [Real.rpow_add hNpos]
      _ = _ := by rw [hexptail]
  calc
    _ ≤ A * (y : ℝ) ^ p + B * (N : ℝ) * (y : ℝ) ^ (-r) := hE M N y hy hyN
    _ ≤ A * (N : ℝ) ^ β + B * ((2 : ℝ) ^ r * (N : ℝ) ^ β) := by
      have hhead' := mul_le_mul_of_nonneg_left hhead hA
      have htail' := mul_le_mul_of_nonneg_left htail hB
      nlinarith
    _ = (A + B * (2 : ℝ) ^ r) * (N : ℝ) ^ β := by ring

end RiemannResearch.Analysis

namespace RiemannResearch.Analysis

/-- Exact feasibility of a physical cutoff `y = n^t` for the three
separate hyperbola majorants. This is exponent arithmetic only: the
corresponding signed prefix and density bounds remain hypotheses. -/
theorem strict_hyperbola_exponent_feasible_iff
    (p a d : ℝ) (hp : (1 : ℝ) / 2 ≤ p) :
    (∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ t * p < 1 / 2 ∧
      1 - t * (1 - a) < 1 / 2 ∧ 1 - t * d < 1 / 2) ↔
      a < 1 - p ∧ p < d := by
  constructor
  · rintro ⟨t, ht, _, hhead, hprefix, hdensity⟩
    have hpa : p < 1 - a := by
      by_contra h
      have hmul := mul_le_mul_of_nonneg_left (le_of_not_gt h) ht.le
      linarith
    have hpd : p < d := by
      by_contra h
      have hmul := mul_le_mul_of_nonneg_left (le_of_not_gt h) ht.le
      linarith
    exact ⟨by linarith, hpd⟩
  · rintro ⟨ha, hd⟩
    let r : ℝ := min (1 - a) d
    have hpr : p < r := lt_min (by linarith) hd
    have hra : r ≤ 1 - a := min_le_left _ _
    have hrd : r ≤ d := min_le_right _ _
    have hs : 0 < p + r := by linarith
    have hs1 : 1 ≤ p + r := by linarith
    have ht : 0 < 1 / (p + r) := div_pos (by norm_num) hs
    have ht1 : 1 / (p + r) ≤ 1 := by
      apply (div_le_iff₀ hs).2
      simpa using hs1
    have hprod : (1 / (p + r)) * (p + r) = 1 := by
      field_simp [ne_of_gt hs]
    have hcmp := mul_lt_mul_of_pos_left hpr ht
    have hhead : (1 / (p + r)) * p < 1 / 2 := by nlinarith
    have hmiddle := mul_le_mul_of_nonneg_left hra ht.le
    have htail := mul_le_mul_of_nonneg_left hrd ht.le
    exact ⟨1 / (p + r), ht, ht1, hhead, by nlinarith, by nlinarith⟩

/-- When the residue head and one other term both have the critical
physical power `n^(1/2)`, a logarithmic cutoff loss can make both squared
majorants summable exactly when the other term saves more than one log. -/
theorem critical_hyperbola_log_feasible_iff
    (p b : ℝ) (hp : 0 < p) :
    (∃ z : ℝ, 0 < z ∧ (1 : ℝ) / 2 < z * p ∧
      1 / 2 < b - z * p) ↔ 1 < b := by
  constructor
  · rintro ⟨z, _, hh, hb⟩
    linarith
  · intro hb
    have hz : 0 < b / (2 * p) := div_pos (by linarith) (by positivity)
    have hzprod : (b / (2 * p)) * p = b / 2 := by
      field_simp [ne_of_gt hp]
    exact ⟨b / (2 * p), hz, by rw [hzprod]; linarith,
      by rw [hzprod]; linarith⟩

/-- At the double critical boundary, the prefix and density savings are
both needed, and each must exceed one. -/
theorem critical_hyperbola_two_logs_feasible_iff
    (p b e : ℝ) (hp : 0 < p) :
    (∃ z : ℝ, 0 < z ∧ (1 : ℝ) / 2 < z * p ∧
      1 / 2 < b - z * p ∧ 1 / 2 < e - z * p) ↔
      1 < b ∧ 1 < e := by
  constructor
  · rintro ⟨z, _, hh, hb, he⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨hb, he⟩
    have hm : 1 < min b e := lt_min hb he
    have hz : 0 < min b e / (2 * p) :=
      div_pos (by linarith) (by positivity)
    have hzprod : (min b e / (2 * p)) * p = min b e / 2 := by
      field_simp [ne_of_gt hp]
    have hmb : min b e ≤ b := min_le_left _ _
    have hme : min b e ≤ e := min_le_right _ _
    refine ⟨min b e / (2 * p), hz, ?_, ?_, ?_⟩
    · rw [hzprod]
      linarith
    · rw [hzprod]
      linarith
    · rw [hzprod]
      linarith

/-- Optimal balancing of `y^p + n*y^(-r)` has power below one half
exactly when the decay exponent exceeds the residue-head exponent. -/
theorem balanced_hyperbola_power_lt_half_iff
    (p r : ℝ) (hs : 0 < p + r) :
    p / (p + r) < (1 : ℝ) / 2 ↔ p < r := by
  rw [div_lt_iff₀ hs]
  constructor <;> intro h <;> linarith

end RiemannResearch.Analysis

namespace RiemannResearch.Analysis

/-- Exact missing gain relative to the powers a=1-ε and d=ε.
This is feasibility of a majorant, not a lower bound on actual energy. -/
theorem subhalf_hyperbola_power_gain_feasible_iff
    (ε δ : ℝ) (hε : ε ≤ 1 / 2) :
    (∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ t * (1 - ε) < 1 / 2 ∧
      1 - t * (1 - (1 - ε - δ)) < 1 / 2 ∧
      1 - t * (ε + δ) < 1 / 2) ↔ 1 - 2 * ε < δ := by
  rw [strict_hyperbola_exponent_feasible_iff (1 - ε) (1 - ε - δ) (ε + δ) (by linarith)]
  constructor
  · intro h
    linarith [h.1]
  · intro h
    constructor <;> linarith

end RiemannResearch.Analysis
