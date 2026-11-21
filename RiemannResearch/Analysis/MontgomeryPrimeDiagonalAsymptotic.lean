/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.MontgomeryPrimeDiagonalAbel
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import RiemannResearch.Analysis.MontgomeryPrimeDiagonalScalar
import RiemannResearch.Analysis.MontgomerySharpEdgeLayer
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import RiemannResearch.Analysis.MontgomeryPrimeDiagonalPrefix
import RiemannResearch.Analysis.MontgomeryPrimeDiagonalTail

/-! The Montgomery prime diagonal: main term, exact signed error, and unconditional rates.
The weight and summatory normalization follow `MontgomeryPrimeDiagonalAbel`.
The two integral evaluations and estimates below give the arithmetic input for the moving edge. -/

open MeasureTheory Set Filter Asymptotics
open scoped BigOperators Topology ArithmeticFunction
noncomputable section
namespace RiemannResearch.Analysis.MontgomeryHorizontalBessel

/-- The integral of the model density `log` from 1 to `t`. -/
def primeDiagonalPrefixModel (t : ℝ) : ℝ := t * Real.log t - t + 1

private def modelHeadPrimitive (t : ℝ) : ℝ :=
  t ^ 2 * Real.log t / 2 - 3 * t ^ 2 / 4 + t

private def modelTailPrimitive (t : ℝ) : ℝ :=
  -(Real.log t / t * t⁻¹) / 2 + (t⁻¹) ^ 2 / 4 - (t⁻¹) ^ 3 / 3

private theorem modelHeadPrimitive_deriv {t : ℝ} (ht : 0 < t) :
    HasDerivAt modelHeadPrimitive (primeDiagonalPrefixModel t) t := by
  have hi := hasDerivAt_id t
  have h := ((((hi.pow 2).mul (Real.hasDerivAt_log ht.ne')).div_const 2).sub
    (((hi.pow 2).const_mul 3).div_const 4)).add hi
  apply h.congr_deriv
  dsimp [primeDiagonalPrefixModel]
  field_simp [ht.ne']
  <;> ring

private theorem modelTailPrimitive_deriv {t : ℝ} (ht : 0 < t) :
    HasDerivAt modelTailPrimitive (primeDiagonalPrefixModel t / t ^ 4) t := by
  have hi := hasDerivAt_id t
  have hinv := hasDerivAt_inv ht.ne'
  have h := (((((Real.hasDerivAt_log ht.ne').div hi ht.ne').mul hinv).neg.div_const 2).add
    ((hinv.pow 2).div_const 4)).sub ((hinv.pow 3).div_const 3)
  apply h.congr_deriv
  dsimp [primeDiagonalPrefixModel]
  field_simp [ht.ne']
  <;> ring

private theorem modelTailPrimitive_tendsto : Tendsto modelTailPrimitive atTop (𝓝 0) := by
  have hi : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hlog : Tendsto (fun t : ℝ => Real.log t / t) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  unfold modelTailPrimitive
  simpa using
    (((hlog.mul hi).neg.div_const 2).add ((hi.pow 2).div_const 4)).sub ((hi.pow 3).div_const 3)

private theorem primeDiagonalPrefixModel_nonneg {t : ℝ} (ht : 0 < t) :
    0 ≤ primeDiagonalPrefixModel t := by
  have h := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos ht) ht.le
  rw [mul_sub, mul_one, mul_inv_cancel₀ ht.ne'] at h
  unfold primeDiagonalPrefixModel
  linarith

theorem primeDiagonal_model_head_integrable {x : ℝ} (_hx : 1 ≤ x) :
    IntegrableOn primeDiagonalPrefixModel (Ioc 1 x) := by
  have hl : ContinuousOn Real.log (Icc 1 x) :=
    Real.continuousOn_log.mono fun t ht => by change t ≠ 0; linarith [ht.1]
  have hc : ContinuousOn primeDiagonalPrefixModel (Icc 1 x) :=
    ((continuousOn_id.mul hl).sub continuousOn_id).add continuousOn_const
  exact hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self

theorem primeDiagonal_model_tail_integrable {x : ℝ} (hx : 1 ≤ x) :
    IntegrableOn (fun t => primeDiagonalPrefixModel t / t ^ 4) (Ioi x) := by
  apply integrableOn_Ioi_deriv_of_nonneg' (g := modelTailPrimitive)
    (l := 0) _ _ modelTailPrimitive_tendsto
  · intro t ht
    exact modelTailPrimitive_deriv (lt_of_lt_of_le (by linarith : 0 < x) ht)
  · intro t ht
    have ht' : 0 < t := lt_trans (by linarith : 0 < x) ht
    exact div_nonneg (primeDiagonalPrefixModel_nonneg ht') (by positivity)

private theorem primeDiagonal_model_tail_eval {x : ℝ} (hx : 1 ≤ x) :
    (∫ t in Ioi x, primeDiagonalPrefixModel t / t ^ 4) = 0 - modelTailPrimitive x := by
  apply integral_Ioi_of_hasDerivAt_of_tendsto' _ (primeDiagonal_model_tail_integrable hx)
    modelTailPrimitive_tendsto
  intro t ht
  exact modelTailPrimitive_deriv (lt_of_lt_of_le (by linarith : 0 < x) ht)

/-- Exact model for the upper-branch mass remaining beyond a cutoff `Y ≥ x`. -/
theorem primeDiagonal_upperBranch_model {x Y : ℝ} (hx : 1 ≤ x) (hY : x ≤ Y) :
    x ^ 2 * (-(primeDiagonalPrefixModel Y) / Y ^ 3 +
      3 * (∫ t in Ioi Y, primeDiagonalPrefixModel t / t ^ 4)) =
      x ^ 2 / Y ^ 2 * (Real.log Y / 2 + 1 / 4) := by
  rw [primeDiagonal_model_tail_eval (hx.trans hY)]
  unfold primeDiagonalPrefixModel modelTailPrimitive
  field_simp [show Y ≠ 0 by linarith]
  ring

theorem primeDiagonal_model_integrals {x : ℝ} (hx : 1 ≤ x) :
    -(∫ t in Ioc 1 x, primeDiagonalPrefixModel t) / x ^ 2 +
        3 * x ^ 2 * (∫ t in Ioi x, primeDiagonalPrefixModel t / t ^ 4) =
      Real.log x + 1 / (4 * x ^ 2) := by
  have hh : (∫ t in Ioc 1 x, primeDiagonalPrefixModel t) =
      modelHeadPrimitive x - modelHeadPrimitive 1 := by
    rw [← intervalIntegral.integral_of_le hx]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [uIcc_of_le hx] at ht
      exact modelHeadPrimitive_deriv (lt_of_lt_of_le zero_lt_one ht.1)
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).2
        (primeDiagonal_model_head_integrable hx)
  rw [hh, primeDiagonal_model_tail_eval hx]
  simp only [modelHeadPrimitive, modelTailPrimitive, Real.log_one]
  field_simp [show x ≠ 0 by linarith]
  ring


/-- Integrate a pointwise linear envelope against the upper Abel weight. -/
theorem diagonal_tail_error_bound {E : ℝ → ℝ} {x U : ℝ} (hx : 0 < x)
    (hU : ∀ t : ℝ, x < t → |E t| ≤ U * t) :
    |∫ t in Ioi x, E t / t ^ 4| ≤ U / (2 * x ^ 2) := by
  have h := integrableOn_Ioi_rpow_of_lt (a := (-3 : ℝ)) (by norm_num) hx
  have hle : ∀ᵐ t ∂volume.restrict (Ioi x), ‖E t / t ^ 4‖ ≤ U * t ^ (-3 : ℝ) := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
    have ht' : x < t := ht
    have hp := lt_trans hx ht'
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hp 4), Real.rpow_neg hp.le]
    norm_num
    calc
      |E t| / t ^ 4 ≤ (U * t) / t ^ 4 := div_le_div_of_nonneg_right (hU t ht') (by positivity)
      _ = _ := by field_simp [hp.ne']
  have hb := MeasureTheory.norm_integral_le_of_norm_le (h.const_mul U) hle
  rw [Real.norm_eq_abs, integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hx] at hb
  convert hb using 1
  norm_num [Real.rpow_neg hx.le]
  ring

private theorem diagonal_abs_integral_linear {E : ℝ → ℝ} {a b C : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hC : 0 ≤ C)
    (h : ∀ t ∈ Ioc a b, |E t| ≤ C * t) :
    |∫ t in a..b, E t| ≤ C * b ^ 2 := by
  have hbound : ∀ t ∈ uIoc a b, ‖E t‖ ≤ C * b := by
    rw [uIoc_of_le hab]
    intro t ht
    exact (h t ht).trans (mul_le_mul_of_nonneg_left ht.2 hC)
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at hb
  exact hb.trans (by nlinarith [mul_nonneg (mul_nonneg hC (ha.trans hab)) ha])

/-- Control the full kernel by separate linear envelopes below the square root,
above the square root, and beyond the matching frequency. -/
private theorem diagonal_weighted_error_split {E : ℝ → ℝ} {C U W x : ℝ}
    (hC : 0 ≤ C) (hU : 0 ≤ U) (hx : 4 ≤ x)
    (hint : ∀ a b : ℝ, 1 ≤ a → a ≤ b → IntervalIntegrable E volume a b)
    (hlin : ∀ t : ℝ, 2 ≤ t → |E t| ≤ C * t)
    (hmid : ∀ t : ℝ, Real.sqrt x ≤ t → |E t| ≤ U * t)
    (hend : ∀ t : ℝ, x ≤ t → |E t| ≤ W * t) :
    |1 / (4 * x ^ 2) - (∫ t in Ioc 1 x, E t) / x ^ 2
      + 3 * x ^ 2 * (∫ t in Ioi x, E t / t ^ 4)| ≤
      1 / (4 * x ^ 2) + |∫ t in Ioc 1 2, E t| / x ^ 2 + C / x + (U + 3 * W / 2) := by
  have hx0 : 0 < x := by linarith
  have h2 : 2 ≤ Real.sqrt x := by
    rw [← Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hs : Real.sqrt x ≤ x := by
    nlinarith [Real.sq_sqrt hx0.le, Real.sqrt_nonneg x]
  have h₁ := diagonal_abs_integral_linear (E := E) (by norm_num : (0:ℝ) ≤ 2)
    h2 hC (fun t ht => hlin t ht.1.le)
  rw [Real.sq_sqrt hx0.le] at h₁
  have h₂ := diagonal_abs_integral_linear (E := E) (Real.sqrt_nonneg x) hs hU
    (fun t ht => hmid t ht.1.le)
  have h₃ := diagonal_tail_error_bound (E := E) hx0 (fun t ht => hend t ht.le)
  have hsplit : (∫ t in Ioc 1 x, E t) =
      (∫ t in Ioc 1 2, E t) + (∫ t in 2..Real.sqrt x, E t) +
        (∫ t in Real.sqrt x..x, E t) := by
    rw [← intervalIntegral.integral_of_le (by linarith : (1:ℝ) ≤ x),
      ← intervalIntegral.integral_of_le (by norm_num : (1:ℝ) ≤ 2),
      intervalIntegral.integral_add_adjacent_intervals (hint 1 2 le_rfl (by norm_num))
        (hint 2 _ (by norm_num) h2),
      intervalIntegral.integral_add_adjacent_intervals (hint 1 _ le_rfl (by linarith))
        (hint _ _ (by linarith) hs)]
  have hhead : |∫ t in Ioc 1 x, E t| ≤ |∫ t in Ioc 1 2, E t| + C * x +
      U * x ^ 2 := by
    rw [hsplit]
    exact (abs_add_le ..).trans (add_le_add ((abs_add_le ..).trans
      (add_le_add (le_refl _) h₁)) h₂)
  have htotal := (abs_add_le (1 / (4 * x ^ 2) - (∫ t in Ioc 1 x, E t) / x ^ 2)
    (3 * x ^ 2 * (∫ t in Ioi x, E t / t ^ 4))).trans (add_le_add
      (abs_sub _ _) (le_refl _))
  rw [abs_div, abs_of_pos (by positivity : 0 < 4 * x ^ 2), abs_one,
    abs_div, abs_of_pos (sq_pos_of_pos hx0), abs_mul,
    abs_of_pos (by positivity : 0 < 3 * x ^ 2)] at htotal
  apply htotal.trans
  calc
    _ ≤ 1 / (4 * x ^ 2) + (|∫ t in Ioc 1 2, E t| + C * x +
        U * x ^ 2) / x ^ 2 +
        3 * x ^ 2 * (W / (2 * x ^ 2)) :=
      add_le_add (add_le_add (le_refl _) (div_le_div_of_nonneg_right hhead (sq_nonneg x)))
        (mul_le_mul_of_nonneg_left h₃ (by positivity))
    _ = _ := by
      field_simp [hx0.ne']
      ring

/-- For each inverse-log bound on the summatory error, splitting the head at
`sqrt x` gives an inverse-log estimate of the same order on the full kernel. -/
theorem diagonal_weighted_error_logPow {E : ℝ → ℝ} (k : ℕ) {C K x : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hx : 4 ≤ x)
    (hint : ∀ a b : ℝ, 1 ≤ a → a ≤ b → IntervalIntegrable E volume a b)
    (hlin : ∀ t : ℝ, 2 ≤ t → |E t| ≤ C * t)
    (hlog : ∀ t : ℝ, 2 ≤ t → |E t| ≤ K * t / (Real.log t) ^ k) :
    |1 / (4 * x ^ 2) - (∫ t in Ioc 1 x, E t) / x ^ 2
      + 3 * x ^ 2 * (∫ t in Ioi x, E t / t ^ 4)| ≤
      1 / (4 * x ^ 2) + |∫ t in Ioc 1 2, E t| / x ^ 2 + C / x
        + (2 ^ k + 3 / 2 : ℝ) * K / (Real.log x) ^ k := by
  have hx0 : 0 < x := by linarith
  have h2 : 2 ≤ Real.sqrt x := by
    rw [← Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hlogM (s t : ℝ) (hs2 : 2 ≤ s) (hst : s ≤ t) :
      |E t| ≤ (K / (Real.log s) ^ k) * t := by
    have hspos : 0 < Real.log s := Real.log_pos (by linarith)
    have htt : 0 ≤ t := by linarith
    have hle := pow_le_pow_left₀ hspos.le (Real.log_le_log (by linarith) hst) k
    calc
      |E t| ≤ K * t / (Real.log t) ^ k := hlog t (hs2.trans hst)
      _ ≤ K * t / (Real.log s) ^ k :=
        div_le_div_of_nonneg_left (mul_nonneg hK htt) (pow_pos hspos _) hle
      _ = _ := by ring
  have hb := diagonal_weighted_error_split hC
    (div_nonneg hK (pow_nonneg (Real.log_nonneg (by linarith : 1 ≤ Real.sqrt x)) k))
    hx hint hlin (fun t ht => hlogM _ _ h2 ht)
    (fun t ht => hlogM _ _ (by linarith : 2 ≤ x) ht)
  apply hb.trans_eq
  rw [Real.log_sqrt hx0.le, div_pow]
  field_simp [(Real.log_pos (by linarith : 1 < x)).ne']

/-- A square-root-exponential error for the summatory function gives the same
type of error for the whole Abel kernel. The constant is uniform for `log x ≥ 1`
and `x ≥ 4`. -/
theorem diagonal_weighted_error_sqrtLog {E : ℝ → ℝ} {c K x : ℝ} (hc : 0 < c)
    (hK : 0 ≤ K) (hx : 4 ≤ x) (hL : 1 ≤ Real.log x)
    (hint : ∀ a b : ℝ, 1 ≤ a → a ≤ b → IntervalIntegrable E volume a b)
    (h : ∀ t : ℝ, 2 ≤ t → |E t| ≤ K * t * Real.exp (-c * Real.sqrt (Real.log t))) :
    |1 / (4 * x ^ 2) - (∫ t in Ioc 1 x, E t) / x ^ 2
      + 3 * x ^ 2 * (∫ t in Ioi x, E t / t ^ 4)| ≤
      (1 + |∫ t in Ioc 1 2, E t| + K + 5 * K / 2) *
        Real.exp (-(min (c / 2) 1) * Real.sqrt (Real.log x)) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have h2 : 2 ≤ Real.sqrt x := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hs : Real.sqrt x ≤ x := by
    nlinarith [Real.sq_sqrt hx0.le, Real.sqrt_nonneg x]
  let d := min (c / 2) 1
  let u := Real.exp (-d * Real.sqrt (Real.log x))
  have hlin (t : ℝ) (ht : 2 ≤ t) : |E t| ≤ K * t := by
    refine (h t ht).trans ?_
    exact mul_le_of_le_one_right (mul_nonneg hK (by linarith))
      (Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (Real.sqrt_nonneg _)))
  have hm (t : ℝ) (ht : Real.sqrt x ≤ t) : |E t| ≤ (K * u) * t := by
    have hup : Real.exp (-c * Real.sqrt (Real.log t)) ≤ u := by
      apply (diagonal_rootExp_mono_from_sqrt hc.le hx1 ht).trans
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
        (neg_le_neg (min_le_left _ _)) (Real.sqrt_nonneg _))
    calc
      _ ≤ K * t * Real.exp (-c * Real.sqrt (Real.log t)) := h t (h2.trans ht)
      _ ≤ K * t * u := mul_le_mul_of_nonneg_left hup (mul_nonneg hK (by linarith))
      _ = _ := by ring
  have hb := diagonal_weighted_error_split hK (mul_nonneg hK (Real.exp_pos _).le)
    hx hint hlin hm (fun t ht => hm t (hs.trans ht))
  have hlp : 0 ≤ Real.log x := by linarith
  have hsq : Real.sqrt (Real.log x) ≤ Real.log x := by
    nlinarith [Real.sqrt_nonneg (Real.log x), Real.sq_sqrt hlp]
  have hex : 1 / x ≤ u := by
    calc
      1 / x = Real.exp (-(Real.log x)) := by rw [Real.exp_neg, Real.exp_log hx0, one_div]
      _ ≤ Real.exp (-d * Real.sqrt (Real.log x)) := by
        apply Real.exp_le_exp.mpr
        have hab := mul_le_mul_of_nonneg_right (show d ≤ 1 by exact min_le_right _ _)
          (Real.sqrt_nonneg (Real.log x))
        linarith
  have hdown : 1 / (4 * x ^ 2) ≤ u := by
    apply le_trans _ hex
    apply one_div_le_one_div_of_le hx0
    nlinarith [mul_nonneg hx0.le (show 0 ≤ x - 1 by linarith)]
  have hid : 1 / x ^ 2 ≤ u := by
    apply le_trans _ hex
    apply one_div_le_one_div_of_le hx0
    nlinarith [mul_nonneg hx0.le (show 0 ≤ x - 1 by linarith)]
  have hbnd := mul_le_mul_of_nonneg_left hid (abs_nonneg (∫ t in Ioc 1 2, E t))
  have hcnd := mul_le_mul_of_nonneg_left hex hK
  apply hb.trans
  rw [← mul_div_assoc, mul_one] at hbnd hcnd
  calc
    _ ≤ u + |∫ t in Ioc 1 2, E t| * u + K * u + (K * u + 3 * (K * u) / 2) :=
      add_le_add (add_le_add (add_le_add hdown hbnd) hcnd) (le_refl _)
    _ = (1 + |∫ t in Ioc 1 2, E t| + K + 5 * K / 2) * u := by ring


private theorem diagonal_logPow_compress {f : ℝ → ℝ} (k : ℕ) {A B Q : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ x : ℝ, 4 ≤ x → |f x| ≤ 1 / (4 * x ^ 2) + A / x ^ 2 + B / x + Q / (Real.log x) ^ k) :
    f =O[atTop] (fun x : ℝ => 1 / (Real.log x) ^ k) := by
  apply IsBigO.of_bound (1 + A + B + Q)
  have he := (isLittleO_log_rpow_rpow_atTop (k : ℝ) (s := 1) zero_lt_one).eventuallyLE
  filter_upwards [eventually_ge_atTop (4 : ℝ), he] with x hx hk
  have hx' : 0 < x := by linarith
  have hl := Real.log_pos (by linarith : 1 < x)
  have hp := pow_pos hl k
  simp only [Real.rpow_natCast, Real.rpow_one, Real.norm_eq_abs,
    abs_of_pos hp, abs_of_pos hx'] at hk
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hp)]
  have hx2 : x ≤ x ^ 2 := by nlinarith
  have hc : (Real.log x) ^ k ≤ 4 * x ^ 2 := by linarith
  have h1 := one_div_le_one_div_of_le hp hc
  have h2 := div_le_div_of_nonneg_left hA hp (hk.trans hx2)
  have h3 := div_le_div_of_nonneg_left hB hp hk
  calc
    |f x| ≤ _ := h x hx
    _ ≤ 1 / (Real.log x) ^ k + A / (Real.log x) ^ k + B / (Real.log x) ^ k + Q / (Real.log x) ^ k :=
      add_le_add (add_le_add (add_le_add h1 h2) h3) le_rfl
    _ = _ := by ring


/-- Signed difference between the squared von Mangoldt prefix and its continuous model. -/
def primeDiagonalPrefixError (t : ℝ) : ℝ :=
  (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, Λ n ^ 2) - primeDiagonalPrefixModel t

/-- Exact transfer of the summatory error through both branches of the prime diagonal. -/
theorem primeDiagonal_sub_log_eq_error_integrals {x : ℝ} (hx : 1 ≤ x) :
    primeDiagonal x - Real.log x =
      1 / (4 * x ^ 2) - (∫ t in Ioc 1 x, primeDiagonalPrefixError t) / x ^ 2
        + 3 * x ^ 2 * (∫ t in Ioi x, primeDiagonalPrefixError t / t ^ 4) := by
  have hA := primeDiagonal_eq_prefix_integrals hx
  have hB := primeDiagonal_model_integrals hx
  have hs : (∫ t in Ioc 1 x, primeDiagonalPrefixError t) =
      (∫ t in Ioc 1 x, ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, Λ n ^ 2) -
      (∫ t in Ioc 1 x, primeDiagonalPrefixModel t) :=
    integral_sub (mangoldtSquarePrefix_integrableOn_Ioc x) (primeDiagonal_model_head_integrable hx)
  have ht : (∫ t in Ioi x, primeDiagonalPrefixError t / t ^ 4) =
      (∫ t in Ioi x, (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, Λ n ^ 2) / t ^ 4) -
      (∫ t in Ioi x, primeDiagonalPrefixModel t / t ^ 4) := by
    simp only [primeDiagonalPrefixError, sub_div]
    exact integral_sub (mangoldtSquarePrefix_div_four_integrableOn_Ioi hx)
      (primeDiagonal_model_tail_integrable hx)
  rw [hs, ht, hA]
  linear_combination hB

private theorem primeDiagonalPrefixError_intervalIntegrable (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) :
      IntervalIntegrable primeDiagonalPrefixError volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact ((mangoldtSquarePrefix_integrableOn_Ioc b).sub
      (primeDiagonal_model_head_integrable (ha.trans hab))).mono_set
        (fun t ht => ⟨lt_of_le_of_lt ha ht.1, ht.2⟩)

/-- Root-log exponential accuracy from the repository's classical quantitative PNT. -/
theorem primeDiagonal_sub_log_isBigO_sqrtLog :
    ∃ d : ℝ, 0 < d ∧ (fun x : ℝ => primeDiagonal x - Real.log x) =O[atTop]
      (fun x : ℝ => Real.exp (-d * Real.sqrt (Real.log x))) := by
  obtain ⟨c, hc, K, hK, h⟩ := mangoldtSquare_error_sqrtLog
  refine ⟨min (c / 2) 1, lt_min (half_pos hc) zero_lt_one, ?_⟩
  apply IsBigO.of_bound (1 + |∫ t in Ioc 1 2, primeDiagonalPrefixError t| + K + 5 * K / 2)
  filter_upwards [eventually_ge_atTop (4:ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1]
    with x hx hl
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [primeDiagonal_sub_log_eq_error_integrals (by linarith : 1 ≤ x)]
  exact diagonal_weighted_error_sqrtLog hc hK hx hl primeDiagonalPrefixError_intervalIntegrable h

/-- The prime diagonal has arbitrarily high fixed inverse-log accuracy. -/
theorem primeDiagonal_sub_log_isBigO_logPow (k : ℕ) :
    (fun x : ℝ => primeDiagonal x - Real.log x) =O[atTop] (fun x : ℝ => 1 / (Real.log x) ^ k) := by
  obtain ⟨C, hC, hlin⟩ := mangoldtSquare_error_logPow 0
  obtain ⟨K, hK, hlog⟩ := mangoldtSquare_error_logPow k
  apply diagonal_logPow_compress k
    (A := |∫ t in Ioc 1 2, primeDiagonalPrefixError t|)
    (B := C) (Q := ((2:ℝ) ^ k + 3 / 2) * K) (abs_nonneg _) hC
  intro x hx
  rw [primeDiagonal_sub_log_eq_error_integrals (by linarith : 1 ≤ x)]
  apply diagonal_weighted_error_logPow k hC hK hx primeDiagonalPrefixError_intervalIntegrable
  · intro t ht
    simpa [primeDiagonalPrefixError, primeDiagonalPrefixModel] using hlin t ht
  · exact hlog

/-- Unconditional provider of the scalar prime-diagonal asymptotic. -/
theorem primeDiagonalAsymptotic_unconditional : PrimeDiagonalAsymptotic := by
  have h : Tendsto (fun x : ℝ => 1 / (Real.log x) ^ 1) atTop (𝓝 0) := by
    simpa [one_div, Function.comp_def] using (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop)
  exact (primeDiagonal_sub_log_isBigO_logPow 1).trans_tendsto h

/-- The diagonal bound used in the narrow-transition estimates. -/
theorem primeDiagonalBound_unconditional : PrimeDiagonalBound :=
  primeDiagonalBound_of_asymptotic primeDiagonalAsymptotic_unconditional

end RiemannResearch.Analysis.MontgomeryHorizontalBessel

namespace RiemannResearch.Analysis.MontgomeryHorizontalTransfer

open MontgomeryHorizontalBessel

/-- The moving-edge limit with just the smoothing and height-transfer inputs. -/
theorem sharpFormFactor_edge_uniform_of_smoothing_and_transfer {ι : Type*} {l : Filter ι}
    (T H : ι → ℝ) (b c : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hT : Tendsto T l atTop) (hH : Tendsto (fun i => H i / Real.log (T i)) l (𝓝 0))
    (h : ∀ᶠ i in l, ∀ x ∈ Icc (T i) (T i * H i),
      |primeSignalEnergy (T i) x - T i * primeDiagonal x| ≤
        b * x * (1 + Real.log ((T i * Real.log (T i)) / x)) ∧
      |T i * Real.log (T i) * sharpFormFactor (T i) (Real.log x / Real.log (T i)) -
        primeSignalEnergy (T i) x| ≤ c * x) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ x ∈ Icc (T i) (T i * H i),
      |sharpFormFactor (T i) (Real.log x / Real.log (T i)) - 1| < ε := by
  obtain ⟨a, _, ha⟩ := primeDiagonalBound_unconditional
  apply sharpFormFactor_edge_uniform_of_optimized_errors T H a b c hb hc hT hH
  filter_upwards [h, hT.eventually (eventually_ge_atTop (2 : ℝ))] with i hi ht
  intro x hx
  exact ⟨ha x (ht.trans hx.1), hi x hx⟩

end RiemannResearch.Analysis.MontgomeryHorizontalTransfer

namespace RiemannResearch.Analysis.MontgomeryHorizontalBessel

/-- Abel's formula for the mass strictly beyond the upper cutoff. -/
theorem primeDiagonal_upperBranch_eq_prefix_tail {Y : ℝ} (hY : 1 ≤ Y) :
    (∑' n : ℕ, if Y < (n : ℝ) then (Λ n) ^ 2 / (n : ℝ) ^ 3 else 0) =
      -(∑ n ∈ Finset.Icc 0 ⌊Y⌋₊, (Λ n) ^ 2) / Y ^ 3 +
        3 * (∫ t in Ioi Y, (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, (Λ n) ^ 2) / t ^ 4) := by
  have hYp := zero_lt_one.trans_le hY
  let correction (n : ℕ) : ℝ := if (n : ℝ) ≤ Y then - ((Λ n) ^ 2 / Y ^ 3) else 0
  have hzero (n : ℕ) (hn : n ∉ Finset.Icc 0 ⌊Y⌋₊) : correction n = 0 :=
    if_neg fun h => hn (Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.le_floor h⟩)
  have hsum : (∑' n, correction n) = -(∑ n ∈ Finset.Icc 0 ⌊Y⌋₊, (Λ n) ^ 2) / Y ^ 3 := by
    rw [tsum_eq_sum hzero, neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    exact if_pos ((Nat.le_floor_iff hYp.le).mp (Finset.mem_Icc.mp hn).2)
  rw [prefix_tail_eq_tsum hY, ← hsum, ← tsum_mul_left,
    ← ((summable_of_ne_finset_zero hzero).tsum_add ((mangoldtSquare_maxKernel_summable hY).mul_left 3))]
  apply tsum_congr
  intro n
  by_cases hn : (n : ℝ) ≤ Y
  · simp only [correction, if_pos hn, if_neg (not_lt.mpr hn), max_eq_left hn]
    field_simp [hYp.ne'] <;> ring
  · have h := lt_of_not_ge hn
    simp only [correction, if_neg hn, if_pos h, max_eq_right h.le, zero_add]
    field_simp [(hYp.trans h).ne'] <;> ring

/-- Exact signed upper-branch truncation error about its logarithmic model. -/
theorem primeDiagonal_upperBranch_error {x Y : ℝ} (hx : 1 ≤ x) (hY : x ≤ Y) :
    x ^ 2 * (∑' n : ℕ, if Y < (n : ℝ) then (Λ n) ^ 2 / (n : ℝ) ^ 3 else 0) -
      x ^ 2 / Y ^ 2 * (Real.log Y / 2 + 1 / 4) =
      x ^ 2 * (-primeDiagonalPrefixError Y / Y ^ 3 +
        3 * (∫ t in Ioi Y, primeDiagonalPrefixError t / t ^ 4)) := by
  have hy := hx.trans hY
  have hi : (∫ t in Ioi Y, primeDiagonalPrefixError t / t ^ 4) =
      (∫ t in Ioi Y, (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, (Λ n) ^ 2) / t ^ 4) -
      (∫ t in Ioi Y, primeDiagonalPrefixModel t / t ^ 4) := by
    simp only [primeDiagonalPrefixError, sub_div]
    exact integral_sub (mangoldtSquarePrefix_div_four_integrableOn_Ioi hy)
      (primeDiagonal_model_tail_integrable hy)
  rw [primeDiagonal_upperBranch_eq_prefix_tail hy, ← primeDiagonal_upperBranch_model hx hY, hi]
  unfold primeDiagonalPrefixError
  ring

/-- Uniform cutoff bound from a pointwise envelope on the summatory error. -/
theorem primeDiagonal_upperBranch_error_le {x Y U : ℝ} (hx : 1 ≤ x) (hY : x ≤ Y)
    (hU : ∀ t : ℝ, Y ≤ t → |primeDiagonalPrefixError t| ≤ U * t) :
    |x ^ 2 * (∑' n : ℕ, if Y < (n : ℝ) then (Λ n) ^ 2 / (n : ℝ) ^ 3 else 0) -
      x ^ 2 / Y ^ 2 * (Real.log Y / 2 + 1 / 4)| ≤ (5 / 2) * U * (x ^ 2 / Y ^ 2) := by
  have hp : 0 < Y := zero_lt_one.trans_le (hx.trans hY)
  have ht := diagonal_tail_error_bound (E := primeDiagonalPrefixError) hp
    (fun t ht => hU t ht.le)
  rw [primeDiagonal_upperBranch_error hx hY, abs_mul, abs_of_nonneg (sq_nonneg x)]
  calc
    _ ≤ x ^ 2 * (U * Y / Y ^ 3 + 3 * (U / (2 * Y ^ 2))) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg x)
      apply (abs_add_le ..).trans
      rw [abs_div, abs_neg, abs_of_pos (pow_pos hp 3), abs_mul, abs_of_pos (by norm_num : 0 < (3:ℝ))]
      exact add_le_add (div_le_div_of_nonneg_right (hU Y le_rfl) (pow_nonneg hp.le 3))
        (mul_le_mul_of_nonneg_left ht (by norm_num))
    _ = _ := by field_simp [hp.ne']; ring


/-- A uniform estimate for the omitted upper branch, also valid at prime-power cutoffs. -/
theorem primeDiagonal_upperBranch_sqrtLog :
    ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ x Y : ℝ, 1 ≤ x → x ≤ Y → 2 ≤ Y →
      |x ^ 2 * (∑' n : ℕ, if Y < (n : ℝ) then (Λ n) ^ 2 / (n : ℝ) ^ 3 else 0) -
        x ^ 2 / Y ^ 2 * (Real.log Y / 2 + 1 / 4)| ≤
        (5 / 2 * K) * (x ^ 2 / Y ^ 2) * Real.exp (-c * Real.sqrt (Real.log Y)) := by
  obtain ⟨c, hc, K, hK, h⟩ := mangoldtSquare_error_sqrtLog
  refine ⟨c, hc, K, hK, ?_⟩
  intro x Y hx hY hY2
  have hp : 0 < Y := by linarith
  have hen (t : ℝ) (ht : Y ≤ t) :
      |primeDiagonalPrefixError t| ≤ (K * Real.exp (-c * Real.sqrt (Real.log Y))) * t := by
    have hs := Real.sqrt_le_sqrt (Real.log_le_log hp ht)
    have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hs (neg_nonpos.mpr hc.le))
    have hpos : 0 ≤ K * t := mul_nonneg hK (hp.le.trans ht)
    calc
      _ ≤ K * t * Real.exp (-c * Real.sqrt (Real.log t)) := h t (hY2.trans ht)
      _ ≤ K * t * Real.exp (-c * Real.sqrt (Real.log Y)) := mul_le_mul_of_nonneg_left he hpos
      _ = _ := by ring
  have hb := primeDiagonal_upperBranch_error_le hx hY hen
  exact hb.trans_eq (by ring)

end RiemannResearch.Analysis.MontgomeryHorizontalBessel
