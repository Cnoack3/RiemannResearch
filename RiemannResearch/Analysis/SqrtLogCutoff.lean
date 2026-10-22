import RiemannResearch.Analysis.MovingBandAsymptotics
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
Scalar cutoff for transferring arbitrarily strong fixed logarithmic
endpoint rates through increasing-weight Abel summation. This file uses
no arithmetic input.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.Analysis

def sqrtLogCutoff (M : ℕ) : ℕ :=
  ⌊Real.exp (Real.sqrt (Real.log ((M + 1 : ℕ) : ℝ)))⌋₊

theorem sqrtLogCutoff_log_bounds (M : ℕ) :
    Real.sqrt (Real.log ((M + 1 : ℕ) : ℝ)) ≤
      Real.log ((sqrtLogCutoff M + 1 : ℕ) : ℝ) ∧
    Real.log ((sqrtLogCutoff M + 1 : ℕ) : ℝ) ≤
      Real.sqrt (Real.log ((M + 1 : ℕ) : ℝ)) + Real.log 2 := by
  let y := Real.sqrt (Real.log ((M + 1 : ℕ) : ℝ))
  have hy : 0 ≤ y := Real.sqrt_nonneg _
  have hexp : 1 ≤ Real.exp y := Real.one_le_exp_iff.mpr hy
  have hj : (Real.exp y) < ((sqrtLogCutoff M + 1 : ℕ) : ℝ) := by
    simpa only [sqrtLogCutoff, Nat.cast_add, Nat.cast_one, y] using
      Nat.lt_floor_add_one (Real.exp y)
  have hj' : ((sqrtLogCutoff M + 1 : ℕ) : ℝ) ≤ 2 * Real.exp y := by
    have hf := Nat.floor_le (Real.exp_pos y).le
    change ((⌊Real.exp y⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * Real.exp y
    rw [Nat.cast_add, Nat.cast_one]
    linarith
  constructor
  · have h := Real.log_le_log (Real.exp_pos y) hj.le
    simpa only [Real.log_exp] using h
  · have h := Real.log_le_log (by positivity : 0 < ((sqrtLogCutoff M + 1 : ℕ) : ℝ)) hj'
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero y),
      Real.log_exp] at h
    simpa only [add_comm] using h

theorem shifted_log_sqrt_bound (x : ℝ) (hx : 0 ≤ x) :
    Real.log (6 + x) ≤ 2 * Real.log (6 + Real.sqrt x) := by
  have hsq := Real.sq_sqrt hx
  have hn := Real.sqrt_nonneg x
  have h := Real.log_le_log (by positivity : 0 < 6 + x)
    (show 6 + x ≤ (6 + Real.sqrt x) ^ 2 by nlinarith)
  simpa only [Real.log_pow, Nat.cast_ofNat] using h

/-- The cutoff lies strictly inside the conductor for all sufficiently
large conductors. This successor form aligns with prefixes indexed by
the number of included terms. -/
theorem sqrtLogCutoff_succ_le_eventually
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop) :
    ∀ᶠ j in atTop, sqrtLogCutoff (M j) + 1 ≤ M j := by
  let x : ℕ → ℝ := fun j => Real.log ((M j + 1 : ℕ) : ℝ)
  let y : ℕ → ℝ := fun j => Real.sqrt (x j)
  have hx : Tendsto x atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hM))
  filter_upwards [hx.eventually (eventually_gt_atTop (4 : ℝ))] with j hj
  have hxn : 0 ≤ x j := by linarith
  have hyn : 0 ≤ y j := Real.sqrt_nonneg _
  have hsq : (y j) ^ 2 = x j := Real.sq_sqrt hxn
  have hy2 : 2 < y j := by
    have hs4 : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    simpa only [hs4] using (Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 4) hj)
  have hyx : y j + 1 < x j := by nlinarith [sq_nonneg (y j - 1)]
  have he := Real.exp_lt_exp.mpr hyx
  rw [Real.exp_add] at he
  have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hey : 1 ≤ Real.exp (y j) := Real.one_le_exp_iff.mpr hyn
  have hem := mul_le_mul_of_nonneg_left he1 (Real.exp_pos (y j)).le
  have hpos : (0 : ℝ) < ((M j + 1 : ℕ) : ℝ) := by positivity
  have hex : Real.exp (x j) = ((M j + 1 : ℕ) : ℝ) := Real.exp_log hpos
  rw [hex] at he
  have hlt : Real.exp (y j) < (M j : ℝ) := by
    rw [Nat.cast_add, Nat.cast_one] at he
    nlinarith
  have hm : M j ≠ 0 := by
    intro hm
    simp only [x, hm, Nat.zero_add, Nat.cast_one, Real.log_one] at hj
    norm_num at hj
  exact (Nat.floor_lt' hm).mpr hlt

/-- The elementary cutoff facts needed by the split Abel theorem. The
strict inequality k > 2c can always be met by a fixed integer exponent
once endpoint rates are available at every fixed logarithmic order. -/
theorem sqrtLogCutoff_band_facts
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    (δ : ℕ → ℝ) (hδ : ∀ j, 0 ≤ δ j)
    (c k : ℝ) (hc : 0 ≤ c) (hck : c < k / 2)
    (hband : ∀ᶠ j in atTop,
      δ j * Real.log ((M j + 1 : ℕ) : ℝ) ≤
        c * Real.log (6 + Real.log ((M j + 1 : ℕ) : ℝ))) :
    Tendsto (fun j => sqrtLogCutoff (M j)) atTop atTop ∧
    (∀ᶠ j in atTop, sqrtLogCutoff (M j) ≤ M j) ∧
    Tendsto (fun j => ((sqrtLogCutoff (M j) + 1 : ℕ) : ℝ) ^ (δ j))
      atTop (𝓝 1) ∧
    Tendsto (fun j => ((M j + 1 : ℕ) : ℝ) ^ (δ j) *
      (6 + Real.log ((sqrtLogCutoff (M j) + 1 : ℕ) : ℝ)) ^ (-k))
      atTop (𝓝 0) := by
  let x : ℕ → ℝ := fun j => Real.log ((M j + 1 : ℕ) : ℝ)
  let y : ℕ → ℝ := fun j => Real.sqrt (x j)
  let z : ℕ → ℝ := fun j => Real.log ((sqrtLogCutoff (M j) + 1 : ℕ) : ℝ)
  have hxn (j : ℕ) : 0 ≤ x j :=
    Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le (M j)))
  have hyn (j : ℕ) : 0 ≤ y j := Real.sqrt_nonneg _
  have hzn (j : ℕ) : 0 ≤ z j :=
    Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le (sqrtLogCutoff (M j))))
  have hx : Tendsto x atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hM))
  have hy : Tendsto y atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [hx.eventually (eventually_ge_atTop ((max b 0) ^ 2))] with j hj
    calc
      b ≤ max b 0 := le_max_left b 0
      _ = Real.sqrt ((max b 0) ^ 2) := (Real.sqrt_sq (le_max_right b 0)).symm
      _ ≤ y j := Real.sqrt_le_sqrt hj
  have hJ : Tendsto (fun j => sqrtLogCutoff (M j)) atTop atTop :=
    tendsto_nat_floor_atTop.comp (Real.tendsto_exp_atTop.comp hy)
  have hJM : ∀ᶠ j in atTop, sqrtLogCutoff (M j) ≤ M j := by
    filter_upwards [hx.eventually (eventually_gt_atTop (1 : ℝ))] with j hj
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt' (Nat.succ_ne_zero (M j))).mpr
    have hs : y j < x j := Real.sqrt_lt_self_iff.mpr hj
    have he := Real.exp_lt_exp.mpr hs
    simpa only [x, Real.exp_log (show (0 : ℝ) < ((M j + 1 : ℕ) : ℝ) by positivity)] using he
  have hzlo (j : ℕ) : y j ≤ z j := (sqrtLogCutoff_log_bounds (M j)).1
  have hzhi (j : ℕ) : z j ≤ y j + Real.log 2 := (sqrtLogCutoff_log_bounds (M j)).2
  have hlogs (j : ℕ) : Real.log (6 + x j) ≤ 2 * Real.log (6 + y j) :=
    shifted_log_sqrt_bound (x j) (hxn j)
  have hd : Tendsto δ atTop (𝓝 0) := by
    apply damping_shift_tendsto_zero_of_log_margin x δ hx hδ (c + 1)
    exact logarithmic_margin_tendsto_atBot_of_strict_coefficient x δ hx
      (c + 1) c (by linarith) hband
  have hdy : Tendsto (fun j => δ j * y j) atTop (𝓝 0) := by
    have hquot : Tendsto (fun j => (2 * c) * Real.log (6 + y j) / y j)
        atTop (𝓝 0) := by
      simpa only [mul_zero, mul_div_assoc] using
        (tendsto_shifted_log_div_self y hy).const_mul (2 * c)
    apply squeeze_zero' (Eventually.of_forall (fun j => mul_nonneg (hδ j) (hyn j))) _ hquot
    filter_upwards [hy.eventually (eventually_gt_atTop (0 : ℝ)), hband] with j hj hb
    apply (le_div_iff₀ hj).mpr
    have hs : (y j) ^ 2 = x j := Real.sq_sqrt (hxn j)
    have hl := mul_le_mul_of_nonneg_left (hlogs j) hc
    calc
      δ j * y j * y j = δ j * x j := by rw [← hs]; ring
      _ ≤ c * Real.log (6 + x j) := hb
      _ ≤ (2 * c) * Real.log (6 + y j) := by nlinarith
  have hdz : Tendsto (fun j => δ j * z j) atTop (𝓝 0) := by
    have hu : Tendsto (fun j => δ j * y j + δ j * Real.log 2) atTop (𝓝 0) := by
      simpa only [zero_mul, add_zero] using hdy.add (hd.mul_const (Real.log 2))
    apply squeeze_zero' (Eventually.of_forall (fun j => mul_nonneg (hδ j) (hzn j))) _ hu
    exact Eventually.of_forall (fun j => by
      have h := mul_le_mul_of_nonneg_left (hzhi j) (hδ j)
      nlinarith)
  have hhead : Tendsto (fun j => ((sqrtLogCutoff (M j) + 1 : ℕ) : ℝ) ^ (δ j))
      atTop (𝓝 1) := by
    have h := Real.continuous_exp.continuousAt.tendsto.comp hdz
    simp only [Real.exp_zero] at h
    convert h using 1
    funext j
    rw [Real.rpow_def_of_pos (by positivity)]
    dsimp [z]
    congr 1
    ring
  have hk : 0 < k := by linarith
  have hlogz (j : ℕ) : Real.log (6 + x j) ≤ 2 * Real.log (6 + z j) := by
    have h := Real.log_le_log (by linarith [hyn j] : 0 < 6 + y j)
      (show 6 + y j ≤ 6 + z j by linarith [hzlo j])
    linarith [hlogs j]
  have hbound : Tendsto (fun j => (c - k / 2) * Real.log (6 + x j))
      atTop atBot := by
    apply (Real.tendsto_log_atTop.comp
      (tendsto_atTop_add_const_left atTop 6 hx)).const_mul_atTop_of_neg
    linarith
  have hmargin : Tendsto (fun j => δ j * x j - k * Real.log (6 + z j))
      atTop atBot := by
    apply tendsto_atBot.mpr
    intro b
    filter_upwards [tendsto_atBot.mp hbound b, hband] with j hj hb
    have hl := mul_le_mul_of_nonneg_left (hlogz j) hk.le
    nlinarith
  have htail : Tendsto (fun j => ((M j + 1 : ℕ) : ℝ) ^ (δ j) *
      (6 + z j) ^ (-k)) atTop (𝓝 0) := by
    have he : Tendsto (fun j => Real.exp (δ j * x j - k * Real.log (6 + z j)))
        atTop (𝓝 0) := Real.tendsto_exp_comp_nhds_zero.mpr hmargin
    convert he using 1
    funext j
    rw [Real.rpow_def_of_pos (by positivity),
      Real.rpow_def_of_pos (by linarith [hzn j] : 0 < 6 + z j), ← Real.exp_add]
    dsimp [x]
    congr 1
    ring
  exact ⟨hJ, hJM, hhead, htail⟩

end RiemannResearch.Analysis
