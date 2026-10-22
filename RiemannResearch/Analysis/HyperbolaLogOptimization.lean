/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Integer optimization at the critical power/log boundary

The balancing cutoff and its logarithmic lower bound are constructed
explicitly. These are elementary real estimates, independent of arithmetic.
-/

open Filter
open scoped Topology

namespace RiemannResearch.Analysis

/-- Integer realization of the critically balanced power/log cutoff.
The threshold is deliberately generous, to use only elementary logarithm
inequalities. -/
theorem general_critical_log_cutoff
    (p b : ℝ) (hp : (1 : ℝ) / 2 ≤ p) (hp1 : p ≤ 1) (hb : 0 < b)
    {N : ℕ} (hN : 0 < N)
    (hlarge : 64 * (b + 1)^2 + 100 ≤ Real.log (N : ℝ)) :
    ∃ y : ℕ, 0 < y ∧ y ≤ N ∧
      (((N : ℝ) / (6 + Real.log (N : ℝ))^b) ^ (1 / (2*p))) / 2 ≤ (y : ℝ) ∧
      (y : ℝ) ≤ ((N : ℝ) / (6 + Real.log (N : ℝ))^b) ^ (1 / (2*p)) ∧
      (6 + Real.log (N : ℝ)) / 4 ≤ 6 + Real.log (y : ℝ) := by
  let L : ℝ := 6 + Real.log (N : ℝ)
  let θ : ℝ := 1 / (2*p)
  let x : ℝ := ((N : ℝ) / L^b)^θ
  have hp0 : 0 < p := by linarith
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hL100 : 100 ≤ L := by dsimp [L]; nlinarith [sq_nonneg (b+1)]
  have hL : 0 < L := by linarith
  have hLb : 64*b^2 ≤ L := by dsimp [L]; nlinarith
  have hθ : 0 < θ := div_pos (by norm_num) (by positivity)
  have hθlo : (1 : ℝ) / 2 ≤ θ := by
    dsimp [θ]
    apply (le_div_iff₀ (by positivity : 0 < 2*p)).2
    nlinarith
  have hθhi : θ ≤ 1 := by
    dsimp [θ]
    apply (div_le_iff₀ (by positivity : 0 < 2*p)).2
    nlinarith
  have hU : 0 < L^b := Real.rpow_pos_of_pos hL b
  have hbase : 0 < (N : ℝ) / L^b := div_pos hNR hU
  have hx : 0 < x := Real.rpow_pos_of_pos hbase θ
  have hs0 := Real.sqrt_nonneg L
  have hs2 := Real.sq_sqrt hL.le
  have hslarge : 8*b ≤ Real.sqrt L := by nlinarith
  have hlogL : Real.log L ≤ 2 * Real.sqrt L := by
    have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hL)
    have he : Real.log (Real.sqrt L) = (1/2 : ℝ) * Real.log L := by
      rw [Real.sqrt_eq_rpow, Real.log_rpow hL]
    rw [he] at h
    nlinarith
  have hlogsmall : b * Real.log L ≤ L/4 := by
    have hh := mul_le_mul_of_nonneg_left hlogL hb.le
    have hp' := mul_nonneg hs0 (sub_nonneg.mpr hslarge)
    nlinarith
  have hlogdiff : L/2 ≤ Real.log (N : ℝ) - b * Real.log L := by
    have hNL : Real.log (N : ℝ) = L - 6 := by dsimp [L]; ring
    rw [hNL]
    linarith
  have hlogx : Real.log x = θ * (Real.log (N : ℝ) - b * Real.log L) := by
    dsimp [x]
    rw [Real.log_rpow hbase,
      Real.log_div (ne_of_gt hNR) (ne_of_gt hU), Real.log_rpow hL]
  have hlogxlo : L/4 ≤ Real.log x := by
    have hh := mul_le_mul_of_nonneg_left hlogdiff hθ.le
    have hp' := mul_nonneg (sub_nonneg.mpr hθlo) hL.le
    rw [hlogx]
    nlinarith
  have hlogtwo : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hx2 : 2 ≤ x := by
    apply (Real.log_le_log_iff (by norm_num : (0 : ℝ) < 2) hx).mp
    linarith
  let y : ℕ := Nat.floor x
  have hyhi : (y : ℝ) ≤ x := Nat.floor_le hx.le
  have hylo : x/2 ≤ (y : ℝ) := by
    have hh : x < (y : ℝ)+1 := Nat.lt_floor_add_one x
    linarith
  have hyR : (0 : ℝ) < y := (div_pos hx (by norm_num)).trans_le hylo
  have hy : 0 < y := by exact_mod_cast hyR
  have hU1 : 1 ≤ L^b := Real.one_le_rpow (by linarith) hb.le
  have hbaseN : (N : ℝ) / L^b ≤ N := div_le_self hNR.le hU1
  have hxN : x ≤ (N : ℝ) := by
    calc
      _ ≤ (N : ℝ)^θ := Real.rpow_le_rpow hbase.le hbaseN hθ.le
      _ ≤ N := Real.rpow_le_self_of_one_le hN1 hθhi
  have hyN : y ≤ N := by exact_mod_cast hyhi.trans hxN
  have hlogy : L/4 ≤ 6 + Real.log (y : ℝ) := by
    have h := Real.log_le_log (div_pos hx (by norm_num)) hylo
    rw [Real.log_div (ne_of_gt hx) (by norm_num)] at h
    linarith
  exact ⟨y, hy, hyN, by simpa [x, θ, L] using hylo,
    by simpa [x, θ, L] using hyhi, by simpa [L] using hlogy⟩

/-- Exact scalar estimate after selecting the cutoff. The balance identity
`hxbal` is derived from real powers in the final theorem below. -/
theorem general_critical_log_scalar_bound
    (n x y L J p b A B : ℝ)
    (_hn : 0 < n) (hx : 0 < x) (hy : 0 < y)
    (hL : 0 < L) (hJ : 0 < J) (hp : 0 ≤ p) (hb : 0 ≤ b)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hxbal : (x^p)^2 * L^b = n)
    (hylo : x/2 ≤ y) (hyhi : y ≤ x) (hJL : L/4 ≤ J) :
    A*y^p + B*n/(y^p*J^b) ≤
      (A+B*(2:ℝ)^p*(4:ℝ)^b)*x^p := by
  have hq : 0 < x^p := Real.rpow_pos_of_pos hx p
  have hD : 0 < y^p*J^b := mul_pos (Real.rpow_pos_of_pos hy p)
    (Real.rpow_pos_of_pos hJ b)
  have hhead : y^p ≤ x^p := Real.rpow_le_rpow hy.le hyhi hp
  have hylow : x^p ≤ (2:ℝ)^p * y^p := by
    have h := Real.rpow_le_rpow (by positivity : 0 ≤ x/2) hylo hp
    rw [Real.div_rpow hx.le (by norm_num)] at h
    have h' := (div_le_iff₀ (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) p)).mp h
    simpa only [mul_comm] using h'
  have hJlow : L^b ≤ (4:ℝ)^b * J^b := by
    have h := Real.rpow_le_rpow (by positivity : 0 ≤ L/4) hJL hb
    rw [Real.div_rpow hL.le (by norm_num)] at h
    have h' := (div_le_iff₀ (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<4) b)).mp h
    simpa only [mul_comm] using h'
  have hprod : x^p*L^b ≤ ((2:ℝ)^p*y^p)*((4:ℝ)^b*J^b) :=
    mul_le_mul hylow hJlow (by positivity) (by positivity)
  have hnBound : n ≤ ((2:ℝ)^p*(4:ℝ)^b*x^p)*(y^p*J^b) := by
    calc
      _ = x^p*(x^p*L^b) := by rw [← hxbal]; ring
      _ ≤ x^p*(((2:ℝ)^p*y^p)*((4:ℝ)^b*J^b)) :=
        mul_le_mul_of_nonneg_left hprod hq.le
      _ = _ := by ring
  have htail : n/(y^p*J^b) ≤ (2:ℝ)^p*(4:ℝ)^b*x^p :=
    (div_le_iff₀ hD).mpr hnBound
  have hhead' := mul_le_mul_of_nonneg_left hhead hA
  have htail' := mul_le_mul_of_nonneg_left htail hB
  calc
    _ ≤ A*x^p+B*((2:ℝ)^p*(4:ℝ)^b*x^p) := by
      simpa only [mul_div_assoc] using add_le_add hhead' htail'
    _ = _ := by ring

/-- Complete critical-log optimization: the cutoff and balance are proved,
and the only analytic hypothesis is the displayed uniform hyperbola bound.
For `b>1` the resulting envelope has summable Pareto square. -/
theorem eventual_sqrt_log_envelope_of_hyperbola_bound
    (E : ℕ → ℕ → ℝ) (p b A B : ℝ)
    (hp : (1 : ℝ)/2 ≤ p) (hp1 : p ≤ 1) (hb : 1 < b)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hE : ∀ M N y : ℕ, 0 < y → y ≤ N →
      |E M N| ≤ A*(y:ℝ)^p + B*(N:ℝ)/((y:ℝ)^p*(6+Real.log (y:ℝ))^b)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ N : ℕ in atTop, ∀ M : ℕ,
      |E M N| ≤ K * Real.sqrt (N:ℝ) * (6+Real.log (N:ℝ))^(-(b/2)) := by
  have hp0 : 0 < p := by linarith
  have hb0 : 0 < b := by linarith
  have hlog : Tendsto (fun N:ℕ => Real.log (N:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨A+B*(2:ℝ)^p*(4:ℝ)^b, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (1:ℕ),
    hlog.eventually (eventually_ge_atTop (64*(b+1)^2+100))] with N hN hlarge
  intro M
  have hNp : 0 < N := by omega
  have hNR : (0:ℝ)<N := by exact_mod_cast hNp
  have hN1 : (1:ℝ)≤N := by exact_mod_cast hN
  obtain ⟨y, hy, hyN, hylo, hyhi, hJL⟩ :=
    general_critical_log_cutoff p b hp hp1 hb0 hNp hlarge
  let L : ℝ := 6+Real.log (N:ℝ)
  let J : ℝ := 6+Real.log (y:ℝ)
  let θ : ℝ := 1/(2*p)
  let x : ℝ := ((N:ℝ)/L^b)^θ
  have hyR : (0:ℝ)<y := by exact_mod_cast hy
  have hy1 : (1:ℝ)≤y := by exact_mod_cast hy
  have hL : 0<L := by dsimp [L]; linarith [Real.log_nonneg hN1]
  have hJ : 0<J := by dsimp [J]; linarith [Real.log_nonneg hy1]
  have hU : 0<L^b := Real.rpow_pos_of_pos hL b
  have hbase : 0<(N:ℝ)/L^b := div_pos hNR hU
  have hx : 0<x := Real.rpow_pos_of_pos hbase θ
  have hθp : θ*p=(1:ℝ)/2 := by dsimp [θ]; field_simp [ne_of_gt hp0]
  have hxp : x^p = ((N:ℝ)/L^b)^((1:ℝ)/2) := by
    dsimp [x]
    rw [← Real.rpow_mul hbase.le, hθp]
  have hxbal : (x^p)^2 * L^b = N := by
    rw [hxp]
    have hsq : (((N:ℝ)/L^b)^((1:ℝ)/2))^2 = (N:ℝ)/L^b := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hbase.le]
      norm_num
    rw [hsq, div_mul_cancel₀ _ (ne_of_gt hU)]
  have hprofile : x^p = Real.sqrt (N:ℝ) / L^(b/2) := by
    rw [hxp, Real.div_rpow hNR.le hU.le, ← Real.rpow_mul hL.le]
    rw [show b*((1:ℝ)/2)=b/2 by ring, ← Real.sqrt_eq_rpow]
  have hbound := general_critical_log_scalar_bound (N:ℝ) x (y:ℝ) L J p b A B
    hNR hx hyR hL hJ hp0.le hb0.le hA hB hxbal hylo hyhi hJL
  have hfinal := (hE M N y hy hyN).trans hbound
  rw [hprofile] at hfinal
  change |E M N| ≤ (A+B*(2:ℝ)^p*(4:ℝ)^b) *
    Real.sqrt (N:ℝ) * L^(-(b/2))
  rw [Real.rpow_neg hL.le]
  simpa only [div_eq_mul_inv, mul_assoc] using hfinal

end RiemannResearch.Analysis
