/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroOrdinate
import RiemannResearch.RH.WeilExplicitFormula.Assembly
import RiemannResearch.RH.WeilExplicitFormula.GammaFacts.Complete
import RiemannResearch.RH.WeilExplicitFormula.RvM.Statement
import RiemannResearch.RH.WeilExplicitFormula.RvM.NcountWindow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Actual zeta-zero count normalization

The already proved actual Riemann-von Mangoldt theorem
`Zeta23.RvM.riemannVonMangoldt Zeta23.gammaFacts` supplies the dyadic lower
bound. Finite geometric accumulation proves every eventual normalization
`c * T * log T` with `c < 1 / (2*pi)`, including `7 / (16*pi)`.
The earlier `1 / (16*pi)` bound and positivity remain available.
All zeros retain their actual analytic multiplicities. No Landau, density,
or Riemann-Hypothesis premise is used.
-/

open Filter Zeta23

namespace RiemannResearch.Analysis.ActualZeroOrdinate

theorem eventually_count_ge_log :
    ∀ᶠ T : ℝ in atTop, (1 / (16 * Real.pi)) * T * Real.log T ≤
      (Ncount 0 T : ℝ) := by
  have hd := Assembly.eventually_N_ge zetaZeroConfig
    (RvM.riemannVonMangoldt gammaFacts)
  have hh : ∀ᶠ T : ℝ in atTop,
      (T / 2) * l (T / 2) / (4 * Real.pi) ≤ (Ncount (T / 2) T : ℝ) := by
    have hc := (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2)).eventually hd
    filter_upwards [hc] with T hT
    simpa only [id_eq, zetaZeroConfig_N, show 2 * (T / 2) = T by ring] using hT
  filter_upwards [hh, eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop
      (2 * (Real.log 2 + Real.log (2 * Real.pi)))] with T hN hT hL
  have he := Assembly.log_eq_l_add (T := T / 2) (by positivity)
  rw [Real.log_div (ne_of_gt hT) (by norm_num : (2 : ℝ) ≠ 0)] at he
  have hhalf : Real.log T / 2 ≤ l (T / 2) := by linarith
  have hm : (Ncount (T / 2) T : ℝ) ≤ (Ncount 0 T : ℝ) := by
    exact_mod_cast Ncount_mono (a := T / 2) (b := T) (c := 0) (d := T)
      (by linarith) le_rfl
  calc
    _ = T * (Real.log T / 2) / (8 * Real.pi) := by field_simp; ring
    _ ≤ T * l (T / 2) / (8 * Real.pi) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hhalf hT.le) (by positivity)
    _ = (T / 2) * l (T / 2) / (4 * Real.pi) := by field_simp; ring
    _ ≤ _ := hN
    _ ≤ _ := hm

theorem exists_count_normalization :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ T : ℝ in atTop,
      c * T * Real.log T ≤ (Ncount 0 T : ℝ) := by
  exact ⟨1 / (16 * Real.pi), by positivity, eventually_count_ge_log⟩

 theorem eventually_count_pos : ∀ᶠ T : ℝ in Filter.atTop, 0 < Ncount 0 T := by
  filter_upwards [eventually_count_ge_log, Filter.eventually_gt_atTop (1 : ℝ)] with T hN hT
  have hlog : 0 < Real.log T := Real.log_pos hT
  have hp : (0 : ℝ) < (Ncount 0 T : ℝ) := lt_of_lt_of_le (by positivity) hN
  exact_mod_cast hp

end RiemannResearch.Analysis.ActualZeroOrdinate

namespace Zeta23.Assembly

/-- Dyadic Riemann--von Mangoldt gives every lower coefficient strictly below
its main-term coefficient, without a loss in that coefficient. -/
theorem eventually_N_ge_log_of_lt (Z : ZeroConfig) (hR : RiemannVonMangoldt Z)
    {q : ℝ} (hq : q < 1 / (2 * Real.pi)) :
    ∀ᶠ T : ℝ in atTop,
      q * T * Real.log T ≤ (Z.N T (2 * T) : ℝ) := by
  let b : ℝ := 1 / (2 * Real.pi)
  let u : ℝ := -Real.log (2 * Real.pi) + 2 * Real.log 2 - 1
  have hb : 0 < b := by dsimp [b]; positivity
  have hk : 0 < b - q := by
    dsimp [b]
    exact sub_pos.mpr hq
  obtain ⟨C, T₀, hmain⟩ := hR.main
  filter_upwards [eventually_ge_atTop T₀, eventually_gt_atTop (0 : ℝ),
    eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (2 * b * |u| / (b - q)),
    eventually_ge_atTop (2 * |C| / (b - q))]
    with T hT₀ hT hT1 hLu hTC
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hell : ell1 T = Real.log T + u := by
    rw [ell1_eq]
    have he := log_eq_l_add hT
    dsimp [u, c₀]
    linarith
  have hformula : T / (2 * Real.pi) * ell1 T =
      b * T * (Real.log T + u) := by
    rw [hell]
    dsimp [b]
    ring
  have hlow := (abs_le.mp (hmain T hT₀)).1
  rw [hformula] at hlow
  have hu := mul_le_mul_of_nonneg_left (neg_abs_le u)
    (mul_nonneg hb.le hT.le)
  have hC := mul_le_mul_of_nonneg_right (le_abs_self C) hlog
  have hlower : b * T * Real.log T - b * T * |u| - |C| * Real.log T ≤
      (Z.N T (2 * T) : ℝ) := by
    nlinarith [hlow, hu, hC]
  have hu₀ : b * |u| ≤ ((b - q) / 2) * Real.log T := by
    have h := (div_le_iff₀ hk).mp hLu
    nlinarith
  have hC₀ : |C| ≤ ((b - q) / 2) * T := by
    have h := (div_le_iff₀ hk).mp hTC
    nlinarith
  have huT : b * T * |u| ≤ ((b - q) / 2) * T * Real.log T := by
    calc
      _ = T * (b * |u|) := by ring
      _ ≤ T * (((b - q) / 2) * Real.log T) :=
        mul_le_mul_of_nonneg_left hu₀ hT.le
      _ = _ := by ring
  have hCT : |C| * Real.log T ≤ ((b - q) / 2) * T * Real.log T :=
    mul_le_mul_of_nonneg_right hC₀ hlog
  calc
    _ = b * T * Real.log T - ((b - q) / 2) * T * Real.log T -
        ((b - q) / 2) * T * Real.log T := by ring
    _ ≤ b * T * Real.log T - b * T * |u| - |C| * Real.log T := by
      linarith
    _ ≤ _ := hlower

end Zeta23.Assembly

namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- Finite dyadic accumulation. The ratio `3/4` leaves an explicit positive
margin at each induction step to absorb the fixed `log 2` loss. -/
theorem eventually_count_ge_log_geometric {q : ℝ}
    (hq : 0 < q) (hq₁ : q < 1 / (2 * Real.pi)) (n : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      (q * (1 - (3 / 4 : ℝ) ^ n)) * T * Real.log T ≤ (Ncount 0 T : ℝ) := by
  have hd := Assembly.eventually_N_ge_log_of_lt zetaZeroConfig
    (RvM.riemannVonMangoldt gammaFacts) hq₁
  have hh : ∀ᶠ T : ℝ in atTop,
      q * (T / 2) * Real.log (T / 2) ≤ (Ncount (T / 2) T : ℝ) := by
    have hc := (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2)).eventually hd
    filter_upwards [hc] with T hT
    simpa only [id_eq, zetaZeroConfig_N, show 2 * (T / 2) = T by ring] using hT
  induction n with
  | zero =>
    exact Eventually.of_forall fun T => by
      simpa using (Nat.cast_nonneg (Ncount 0 T) : (0 : ℝ) ≤ (Ncount 0 T : ℝ))
  | succ n ih =>
    let a : ℝ := q * (1 - (3 / 4 : ℝ) ^ n)
    let a' : ℝ := q * (1 - (3 / 4 : ℝ) ^ (n + 1))
    let m : ℝ := q * (3 / 4 : ℝ) ^ n / 4
    have hm : 0 < m := by dsimp [m]; positivity
    have hmargin : (q + a) / 2 - a' = m := by
      dsimp [a, a', m]
      rw [pow_succ]
      ring
    have hi := (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2)).eventually ih
    filter_upwards [hi, hh, eventually_gt_atTop (0 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop (((q + a) / 2) * Real.log 2 / m)]
      with T hI hD hT hL
    have hlog : Real.log (T / 2) = Real.log T - Real.log 2 :=
      Real.log_div (ne_of_gt hT) (by norm_num : (2 : ℝ) ≠ 0)
    have hadd : (Ncount 0 T : ℝ) =
        (Ncount 0 (T / 2) : ℝ) + (Ncount (T / 2) T : ℝ) := by
      exact_mod_cast Ncount_add (a := 0) (b := T / 2) (c := T)
        (by linarith) (by linarith)
    change a * (T / 2) * Real.log (T / 2) ≤ (Ncount 0 (T / 2) : ℝ) at hI
    have hbudget : ((q + a) / 2) * Real.log 2 ≤ m * Real.log T := by
      have h := (div_le_iff₀ hm).mp hL
      linarith
    have hidentity : ((q + a) / 2) * (Real.log T - Real.log 2) - a' * Real.log T =
        m * Real.log T - ((q + a) / 2) * Real.log 2 := by
      rw [← hmargin]
      ring
    have hscalar : a' * Real.log T ≤ ((q + a) / 2) * (Real.log T - Real.log 2) := by
      linarith
    change a' * T * Real.log T ≤ (Ncount 0 T : ℝ)
    calc
      _ = T * (a' * Real.log T) := by ring
      _ ≤ T * (((q + a) / 2) * (Real.log T - Real.log 2)) :=
        mul_le_mul_of_nonneg_left hscalar hT.le
      _ = a * (T / 2) * Real.log (T / 2) +
          q * (T / 2) * Real.log (T / 2) := by rw [hlog]; ring
      _ ≤ (Ncount 0 (T / 2) : ℝ) + (Ncount (T / 2) T : ℝ) := add_le_add hI hD
      _ = _ := hadd.symm

/-- Every coefficient strictly below the sharp leading constant is a valid
eventual normalization for the actual zero count, with no RH or density premise. -/
theorem eventually_count_ge_log_of_lt {c : ℝ} (hc : c < 1 / (2 * Real.pi)) :
    ∀ᶠ T : ℝ in atTop, c * T * Real.log T ≤ (Ncount 0 T : ℝ) := by
  by_cases hc₀ : c ≤ 0
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    have hT₀ : 0 ≤ T := by linarith
    have hlog : 0 ≤ Real.log T := Real.log_nonneg hT.le
    calc
      _ = c * (T * Real.log T) := by ring
      _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc₀ (mul_nonneg hT₀ hlog)
      _ ≤ _ := Nat.cast_nonneg _
  have hc₀ : 0 < c := lt_of_not_ge hc₀
  let b : ℝ := 1 / (2 * Real.pi)
  let q : ℝ := (c + b) / 2
  have hb : 0 < b := by dsimp [b]; positivity
  have hcb : c < b := hc
  have hq : 0 < q := by dsimp [q]; linarith
  have hcq : c < q := by dsimp [q]; linarith
  have hqb : q < 1 / (2 * Real.pi) := by
    change q < b
    dsimp [q]
    linarith
  have hgap : 0 < q - c := sub_pos.mpr hcq
  have hx : 1 ≤ q / (q - c) := by
    apply (one_le_div hgap).2
    linarith
  obtain ⟨n, _, hn⟩ := exists_nat_pow_near (x := q / (q - c)) hx
    (by norm_num : (1 : ℝ) < 4 / 3)
  have hn' : q < (4 / 3 : ℝ) ^ (n + 1) * (q - c) :=
    (div_lt_iff₀ hgap).mp hn
  have hp : (3 / 4 : ℝ) ^ (n + 1) * (4 / 3 : ℝ) ^ (n + 1) = 1 := by
    rw [← mul_pow]
    norm_num
  have hsmall : q * (3 / 4 : ℝ) ^ (n + 1) < q - c := by
    calc
      _ = (3 / 4 : ℝ) ^ (n + 1) * q := by ring
      _ < (3 / 4 : ℝ) ^ (n + 1) * ((4 / 3 : ℝ) ^ (n + 1) * (q - c)) :=
        mul_lt_mul_of_pos_left hn' (by positivity)
      _ = ((3 / 4 : ℝ) ^ (n + 1) * (4 / 3 : ℝ) ^ (n + 1)) * (q - c) := by ring
      _ = q - c := by rw [hp, one_mul]
  have hcoeff : c ≤ q * (1 - (3 / 4 : ℝ) ^ (n + 1)) := by nlinarith
  filter_upwards [eventually_count_ge_log_geometric hq hqb (n + 1),
    eventually_gt_atTop (1 : ℝ)] with T hN hT
  have hTlog : 0 ≤ T * Real.log T :=
    mul_nonneg (by linarith) (Real.log_nonneg hT.le)
  calc
    _ = c * (T * Real.log T) := by ring
    _ ≤ (q * (1 - (3 / 4 : ℝ) ^ (n + 1))) * (T * Real.log T) :=
      mul_le_mul_of_nonneg_right hcoeff hTlog
    _ = (q * (1 - (3 / 4 : ℝ) ^ (n + 1))) * T * Real.log T := by ring
    _ ≤ _ := hN

/-- A convenient concrete normalization seven times stronger than the earlier
`1/(16*pi)` lower bound. -/
theorem eventually_count_ge_seven_log :
    ∀ᶠ T : ℝ in atTop, (7 / (16 * Real.pi)) * T * Real.log T ≤ (Ncount 0 T : ℝ) := by
  apply eventually_count_ge_log_of_lt
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
  nlinarith [Real.pi_pos]


open scoped Topology

/-- The height/count ratio vanishes by the unconditional zero-count lower bound. -/
theorem tendsto_height_div_count :
    Tendsto (fun T : ℝ => T / (Ncount 0 T : ℝ)) atTop (𝓝 0) := by
  have hupper : ∀ᶠ T : ℝ in atTop,
      T / (Ncount 0 T : ℝ) ≤ (16 * Real.pi) / Real.log T := by
    filter_upwards [eventually_count_ge_log, eventually_gt_atTop (1 : ℝ)] with T hN hT
    have hTpos : 0 < T := by linarith
    have hL : 0 < Real.log T := Real.log_pos hT
    have hc : 0 < 1 / (16 * Real.pi) := by positivity
    calc
      _ ≤ T / ((1 / (16 * Real.pi)) * T * Real.log T) :=
        div_le_div_of_nonneg_left hTpos.le (by positivity) hN
      _ = (16 * Real.pi) / Real.log T := by field_simp
  refine squeeze_zero' ?_ hupper ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact div_nonneg hT.le (Nat.cast_nonneg _)
  · simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop) :
        Tendsto (fun T : ℝ => (16 * Real.pi) * (Real.log T)⁻¹) atTop (𝓝 ((16 * Real.pi) * 0)))

theorem tendsto_complex_height_div_count :
    Tendsto (fun T : ℝ => (T : ℂ) / (Ncount 0 T : ℂ)) atTop (𝓝 0) := by
  simpa only [Function.comp_def, Complex.ofReal_div, Complex.ofReal_natCast,
    Complex.ofReal_zero] using
      (Complex.continuous_ofReal.tendsto 0).comp tendsto_height_div_count


end RiemannResearch.Analysis.ActualZeroOrdinate
