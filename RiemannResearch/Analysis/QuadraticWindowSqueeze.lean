import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Moving-cutoff squeeze for quadratic Pareto windows

Source: Christian Noack's quadratic-window argument. The estimate explicitly
retains the exterior term. Its rate premise is the one subexponential bound
needed on a proposed cofinal sequence of windows.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.Analysis

private theorem moving_cutoff_budget_le (x k f ε C δ : ℝ)
    (hx : 1 ≤ x) (hf : 1 ≤ f) (hk : f ^ 2 ≤ k) (hk' : k ≤ 2 * f ^ 2)
    (hε : 0 ≤ ε) (hC : 0 ≤ C) (hδ : 0 ≤ δ) :
    (2 + ε * k * (k+2) * (x+1)) * (C * f / x) +
        (1 + 2*x) * (C*f/(k*x) + 2*δ) ≤
      C*(2*(f/x) + 16*(ε*f^5) + 3/f) + 6*(x*δ) := by
  have hx0 : 0 < x := by linarith
  have hf0 : 0 < f := by linarith
  have hk0 : 0 < k := (sq_pos_of_pos hf0).trans_le hk
  have hf2 : 1 ≤ f^2 := by nlinarith [sq_nonneg (f-1)]
  have hkp : k+2 ≤ 4*f^2 := by linarith
  have hxp : x+1 ≤ 2*x := by linarith
  have hxg : 1+2*x ≤ 3*x := by linarith
  have h1 : ε*k*(k+2)*(x+1) ≤ ε*(2*f^2)*(4*f^2)*(2*x) := by gcongr
  have h3 : C*f/k ≤ C/f := by
    rw [div_le_div_iff₀ hk0 hf0]
    calc
      C*f*f = C*f^2 := by ring
      _ ≤ C*k := mul_le_mul_of_nonneg_left hk hC
  calc
    _ ≤ (2 + ε*(2*f^2)*(4*f^2)*(2*x)) * (C*f/x) +
          (3*x)*(C*f/(k*x) + 2*δ) := by gcongr
    _ = C*(2*(f/x) + 16*(ε*f^5)) + 3*(C*f/k) + 6*(x*δ) := by
      field_simp
      ring
    _ ≤ C*(2*(f/x) + 16*(ε*f^5)) + 3*(C/f) + 6*(x*δ) := by gcongr
    _ = _ := by ring

/-- If the concrete moving-cutoff budget holds on a cofinal sequence and
ordinary and reciprocal Möbius cancellation on those windows is of order
`exp (-(5*A+d)*sqrt(log N))` for a fixed `d > 0`, then the bounded nonnegative quantity vanishes. -/
theorem quadratic_window_budget_squeeze
    (N : ℕ → ℕ) (ε δ : ℕ → ℝ) (A d C L E : ℝ)
    (hN : Tendsto N atTop atTop) (hA : 0 < A) (hd : 0 < d) (hC : 0 ≤ C)
    (_hL : 0 ≤ L) (hE : 0 ≤ E)
    (hε : ∀ᶠ j in atTop, 0 ≤ ε j) (hδ : ∀ᶠ j in atTop, 0 ≤ δ j)
    (hM : ∀ᶠ j in atTop, ε j ≤ L * Real.exp (-(5 * A + d) * Real.sqrt (Real.log (N j))))
    (hout : Tendsto (fun j => (N j : ℝ) * δ j) atTop (𝓝 0))
    (hbudget : ∀ᶠ j in atTop,
      let x : ℝ := N j
      let f := Real.exp (A * Real.sqrt (Real.log x))
      let k : ℝ := (⌈f^2⌉₊ : ℕ)
      E ≤ (2 + ε j * k * (k+2) * (x+1)) * (C*f/x) +
        (1+2*x) * (C*f/(k*x) + 2*δ j)) : E = 0 := by
  let t := fun j => Real.sqrt (Real.log (N j : ℝ))
  have hxTop : Tendsto (fun j => (N j : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hN
  have ht : Tendsto t atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp hxTop)
  have hneg : Tendsto (fun j => Real.exp (-t j)) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp ht
  have hnegA : Tendsto (fun j => Real.exp (-(A * t j))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp ((tendsto_const_mul_atTop_of_pos hA).2 ht)
  have hnegD : Tendsto (fun j => Real.exp (-(d * t j))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp ((tendsto_const_mul_atTop_of_pos hd).2 ht)
  have hlim : Tendsto (fun j => C*(2*Real.exp (-t j) + 16*(L*Real.exp (-(d*t j))) +
          3*Real.exp (-(A*t j))) + 6*((N j : ℝ)*δ j)) atTop (𝓝 0) := by
    simpa using ((((hneg.const_mul 2).add ((hnegD.const_mul L).const_mul 16)).add
      (hnegA.const_mul 3)).const_mul C).add (hout.const_mul 6)
  apply le_antisymm _ hE
  apply ge_of_tendsto hlim
  filter_upwards [hbudget, hM, hε, hδ, hxTop.eventually_ge_atTop 1,
    ht.eventually_ge_atTop (A+1)] with j hb hm he hδj hx htj
  let x : ℝ := N j
  let f := Real.exp (A*t j)
  let k : ℝ := (⌈f^2⌉₊ : ℕ)
  change E ≤ (2 + ε j*k*(k+2)*(x+1))*(C*f/x) + (1+2*x)*(C*f/(k*x)+2*δ j) at hb
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hf : 1 ≤ f := Real.one_le_exp (mul_nonneg hA.le (Real.sqrt_nonneg _))
  have hk : f^2 ≤ k := Nat.le_ceil _
  have hk' : k ≤ 2*f^2 := by
    have hk1 : k < f^2+1 := Nat.ceil_lt_add_one (by positivity)
    nlinarith [sq_nonneg (f-1)]
  have hfx : f/x ≤ Real.exp (-t j) := by
    have htsq : t j ^ 2 = Real.log x := Real.sq_sqrt (Real.log_nonneg hx)
    rw [show f/x = Real.exp (A*t j - Real.log x) by rw [Real.exp_sub, Real.exp_log hx0]]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr htj) (Real.sqrt_nonneg (Real.log x))]
  have hεf : ε j * f^5 ≤ L * Real.exp (-(d*t j)) := by
    calc
      _ ≤ (L * Real.exp (-(5*A+d)*t j)) * f^5 :=
        mul_le_mul_of_nonneg_right hm (by positivity)
      _ = _ := by
        dsimp [f]
        rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
        congr 2
        ring
  have hfi : 3/f = 3*Real.exp (-(A*t j)) := by simp [f, Real.exp_neg, div_eq_mul_inv]
  have hbound := moving_cutoff_budget_le x k f (ε j) C (δ j) hx hf hk hk' he hC hδj
  apply hb.trans (hbound.trans _)
  rw [hfi]
  gcongr

end RiemannResearch.Analysis
