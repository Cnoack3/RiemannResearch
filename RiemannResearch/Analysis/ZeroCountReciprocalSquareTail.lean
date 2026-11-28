import RiemannResearch.RH.WeilExplicitFormula.Statement.SeamClosed
import RiemannResearch.RH.WeilExplicitFormula.RvM.NcountWindow
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The reciprocal-square tail of the positive zeta ordinates

The count is right-continuous and counts analytic multiplicities. The
discrepancy used at the end is Corollary 1.2 of Hasanalizade, Shen and Wong,
https://arxiv.org/abs/2107.06506. Its explicit constants enter as a hypothesis.
-/

noncomputable section
open MeasureTheory Set Zeta23
open scoped BigOperators
namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- The Riemann--von Mangoldt main term without its bounded constant. -/
def tailCountMain (t : ℝ) : ℝ :=
  t / (2 * Real.pi) * (Real.log (t / (2 * Real.pi)) - 1)

/-- Upper bound for the positive-ordinate reciprocal-square tail. -/
def reciprocalSquareTailBound (H : ℝ) : ℝ :=
  (Real.log (H / (2 * Real.pi)) + 1) / (2 * Real.pi * H) +
    (2 * Real.log H + 1 / 2) / H ^ 2

private def upperPrimitive (b t : ℝ) : ℝ :=
  -(2 * (Real.log t - Real.log (2 * Real.pi)) / (2 * Real.pi * t) +
    (Real.log t + 1 / 2 - b) / t ^ 2)

private theorem upperPrimitive_deriv (b : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (upperPrimitive b)
      ((tailCountMain t + Real.log t - b) * (2 / t ^ 3)) t := by
  have ha : 2 * Real.pi ≠ 0 := by positivity
  unfold upperPrimitive tailCountMain
  rw [Real.log_div ht.ne' ha]
  have hd := ((((hasDerivAt_const t (2 : ℝ)).mul
    ((Real.hasDerivAt_log ht.ne').sub_const (Real.log (2 * Real.pi)))).div
    ((hasDerivAt_const t (2 * Real.pi)).mul (hasDerivAt_id t))
      (mul_ne_zero ha ht.ne')).add
    ((((Real.hasDerivAt_log ht.ne').add_const (1 / 2 : ℝ)).sub_const b).div
      ((hasDerivAt_id t).pow 2) (pow_ne_zero 2 ht.ne'))).neg
  apply hd.congr_deriv
  simp only [Pi.mul_apply, Pi.pow_apply, id_eq]
  field_simp [ht.ne', Real.pi_ne_zero]
  ring

/-- Kernel integrated from the ordinate to the upper endpoint in Abel summation. -/
def tailStep (y t : ℝ) : ℝ := (Ioi y).indicator (fun x : ℝ => 2 / x ^ 3) t

private theorem tailStep_integrable {H R : ℝ} (hH : 0 < H) (hR : H ≤ R) (y : ℝ) :
    IntervalIntegrable (tailStep y) volume H R := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mpr
  apply IntegrableOn.indicator _ measurableSet_Ioi
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mp
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hR]
  exact continuousOn_const.div (continuous_id.pow 3).continuousOn
    (fun x hx => pow_ne_zero _ (hH.trans_le hx.1).ne')

private theorem tailStep_integral {H y R : ℝ} (hH : 0 < H) (hy : H ≤ y) (hR : y ≤ R) :
    (∫ t in H..R, tailStep y t) = 1 / y ^ 2 - 1 / R ^ 2 := by
  have hyr := hH.trans_le hy
  have hset : Ioi y ∩ Ioc H R = Ioc y R := by
    ext t
    simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
    constructor
    · exact fun h => ⟨h.1, h.2.2⟩
    · exact fun h => ⟨h.1, hy.trans_lt h.1, h.2⟩
  unfold tailStep
  rw [intervalIntegral.integral_of_le (hy.trans hR), integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi, hset, ← intervalIntegral.integral_of_le hR]
  have hd (t : ℝ) (ht : t ∈ uIcc y R) :
      HasDerivAt (fun x : ℝ => -(1 / x ^ 2)) (2 / t ^ 3) t := by
    rw [uIcc_of_le hR] at ht
    have hn := (hyr.trans_le ht.1).ne'
    apply (((hasDerivAt_const t (1 : ℝ)).div ((hasDerivAt_id t).pow 2)
      (pow_ne_zero 2 hn)).neg).congr_deriv
    simp only [Pi.pow_apply, id_eq]
    field_simp [hn]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  · ring
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hR]
    exact continuousOn_const.div (continuous_id.pow 3).continuousOn
      (fun x hx => pow_ne_zero _ (hyr.trans_le hx.1).ne')

/-- Exact layer-cake formula for a finite family above H. -/
theorem finite_ordinate_abel_identity {H R : ℝ} (hH : 0 < H) (hHR : H ≤ R)
    (S : Finset ℂ) (hs : ∀ z ∈ S, H ≤ z.im ∧ z.im ≤ R) :
    ∑ z ∈ S, (zeroMult z : ℝ) / z.im ^ 2 =
      (∑ z ∈ S, (zeroMult z : ℝ)) / R ^ 2 +
        ∫ t in H..R, ∑ z ∈ S, (zeroMult z : ℝ) * tailStep z.im t := by
  rw [intervalIntegral.integral_finsetSum (fun z _ =>
    (tailStep_integrable hH hHR z.im).const_mul (zeroMult z : ℝ)), Finset.sum_div]
  simp_rw [intervalIntegral.integral_const_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  rw [tailStep_integral hH (hs z hz).1 (hs z hz).2]
  ring

private theorem sum_mult_le_count_window {H t : ℝ} (S : Finset ℂ)
    (hs : ∀ z ∈ S, IsNontrivialZero z ∧ H < z.im ∧ z.im ≤ t) :
    ∑ z ∈ S, (zeroMult z : ℝ) ≤ (Ncount H t : ℝ) := by
  have hsub : S ⊆ (zerosIn_finite H t).toFinset := by
    intro z hz
    exact (zerosIn_finite H t).mem_toFinset.mpr (hs z hz)
  have hn := Finset.sum_le_sum_of_subset (f := zeroMult) hsub
  rw [Ncount, finsum_mem_eq_finite_toFinset_sum _ (zerosIn_finite H t)]
  exact_mod_cast hn

/-- A two-sided count estimate gives the claimed upper bound for every finite
subset of the positive-ordinate tail, retaining multiplicity at every root. -/
theorem finite_ordinate_reciprocal_sq_le {H : ℝ} (hH : 2 * Real.pi ≤ H)
    (hc : ∀ t ≥ H, |(Ncount 0 t : ℝ) - tailCountMain t| ≤ Real.log t)
    (S : Finset ℂ) (hs : ∀ z ∈ S, IsNontrivialZero z ∧ H < z.im) :
    ∑ z ∈ S, (zeroMult z : ℝ) / z.im ^ 2 ≤ reciprocalSquareTailBound H := by
  classical
  have ha : 0 < 2 * Real.pi := by positivity
  have h0 := ha.trans_le hH
  obtain ⟨T, hT⟩ := (S.image Complex.im).exists_le
  let R := max H T
  have hHR : H ≤ R := le_max_left _ _
  have hRz (z : ℂ) (hz : z ∈ S) : z.im ≤ R :=
    (hT _ (Finset.mem_image_of_mem _ hz)).trans (le_max_right _ _)
  have hR0 := h0.trans_le hHR
  let b := tailCountMain H - Real.log H
  have hwindow t (ht : H ≤ t) : (Ncount H t : ℝ) ≤ tailCountMain t + Real.log t - b := by
    have hadd : (Ncount 0 t : ℝ) = (Ncount 0 H : ℝ) + (Ncount H t : ℝ) := by
      exact_mod_cast Ncount_add h0.le ht
    have hl := (abs_le.mp (hc H le_rfl)).1
    have hu := (abs_le.mp (hc t ht)).2
    dsimp [b]
    linarith
  have hmass := (sum_mult_le_count_window S
    (fun z hz => ⟨(hs z hz).1, (hs z hz).2, hRz z hz⟩)).trans (hwindow R hHR)
  have hstep t (ht : t ∈ Icc H R) :
      ∑ z ∈ S, (zeroMult z : ℝ) * tailStep z.im t ≤
        (tailCountMain t + Real.log t - b) * (2 / t ^ 3) := by
    have hw := (sum_mult_le_count_window (S.filter (fun z => z.im < t)) (by
      intro z hz
      obtain ⟨hzS, hzt⟩ := Finset.mem_filter.mp hz
      exact ⟨(hs z hzS).1, (hs z hzS).2, hzt.le⟩)).trans (hwindow t ht.1)
    have hsum : ∑ z ∈ S, (zeroMult z : ℝ) * tailStep z.im t =
        (∑ z ∈ S.filter (fun z => z.im < t), (zeroMult z : ℝ)) * (2 / t ^ 3) := by
      rw [Finset.sum_mul, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro z hz
      by_cases h : z.im < t <;> simp [tailStep, Set.indicator, h]
    rw [hsum]
    exact mul_le_mul_of_nonneg_right hw
      (div_nonneg (by norm_num) (pow_nonneg (h0.trans_le ht.1).le _))
  have hi : IntervalIntegrable (fun t => (tailCountMain t + Real.log t - b) * (2 / t ^ 3))
      volume H R := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hHR]
    intro t ht
    have hn := (h0.trans_le ht.1).ne'
    unfold tailCountMain
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  have hiS : IntervalIntegrable (fun t => ∑ z ∈ S, (zeroMult z : ℝ) * tailStep z.im t)
      volume H R := by
    have heq : (∑ z ∈ S, fun t => (zeroMult z : ℝ) * tailStep z.im t) =
        (fun t => ∑ z ∈ S, (zeroMult z : ℝ) * tailStep z.im t) := by
      funext t
      simp only [Finset.sum_apply]
    rw [← heq]
    exact IntervalIntegrable.sum S
      (fun z _ => (tailStep_integrable h0 hHR z.im).const_mul (zeroMult z : ℝ))
  have hInt := intervalIntegral.integral_mono_on hHR hiS hi hstep
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht =>
    upperPrimitive_deriv b (h0.trans_le (by rw [uIcc_of_le hHR] at ht; exact ht.1))) hi] at hInt
  have he := finite_ordinate_abel_identity h0 hHR S (fun z hz => ⟨(hs z hz).2.le, hRz z hz⟩)
  have hlogR := Real.log_nonneg ((one_le_div ha).mpr (hH.trans hHR))
  have hupper : (∑ z ∈ S, (zeroMult z : ℝ)) / R ^ 2 + upperPrimitive b R ≤ 0 := by
    have hm := div_le_div_of_nonneg_right hmass (sq_nonneg R)
    calc
      _ ≤ (tailCountMain R + Real.log R - b) / R ^ 2 + upperPrimitive b R :=
        add_le_add hm le_rfl
      _ = -((Real.log (R / (2 * Real.pi)) + 1) / (2 * Real.pi * R)) - (1 / 2) / R ^ 2 := by
        unfold tailCountMain upperPrimitive
        rw [Real.log_div hR0.ne' ha.ne']
        field_simp [hR0.ne', Real.pi_ne_zero]
        ring
      _ ≤ 0 := by
        have hm₀ : 0 ≤ (Real.log (R / (2 * Real.pi)) + 1) / (2 * Real.pi * R) := by positivity
        linarith [show 0 ≤ (1 / 2 : ℝ) / R ^ 2 by positivity]
  have hbase : -upperPrimitive b H = reciprocalSquareTailBound H := by
    unfold upperPrimitive reciprocalSquareTailBound b tailCountMain
    rw [Real.log_div h0.ne' ha.ne']
    field_simp [h0.ne', Real.pi_ne_zero]
    ring
  linarith

/-- At the Platt--Trudgian height the explicit upper bound is strictly less
than the exact rational 3 / (2 * 10^12). -/
theorem reciprocalSquareTailBound_three_trillion_lt :
    reciprocalSquareTailBound 3000000000000 < 3 / 2000000000000 := by
  have hpi := Real.pi_gt_d2
  have ha : 0 < 2 * Real.pi := by positivity
  have hlog := Real.log_le_log (div_pos (by norm_num : 0 < (3000000000000 : ℝ)) ha)
    (show (3000000000000 : ℝ) / (2 * Real.pi) ≤ 2 ^ 39 by
      apply (div_le_iff₀ ha).2
      norm_num
      linarith)
  have hH := Real.log_le_log (by norm_num : 0 < (3000000000000 : ℝ))
    (by norm_num : (3000000000000 : ℝ) ≤ 2 ^ 42)
  rw [Real.log_pow] at hlog hH
  norm_num only [Nat.cast_ofNat] at hlog hH
  have h₁ : (Real.log (3000000000000 / (2 * Real.pi)) + 1) / (2 * Real.pi * 3000000000000)
      < 1499 / 1000000000000000 := by
    apply (div_lt_iff₀ (by positivity)).2
    linarith [Real.log_two_lt_d9]
  have h₂ : (2 * Real.log 3000000000000 + 1 / 2) / (3000000000000 : ℝ) ^ 2
      < 1 / 1000000000000000 := by
    apply (div_lt_iff₀ (by positivity)).2
    linarith [Real.log_two_lt_d9]
  unfold reciprocalSquareTailBound
  exact (add_lt_add h₁ h₂).trans_le (by norm_num)

/-- The published constants imply the simpler discrepancy bound on the
entire integration range, including its left endpoint. -/
theorem tailCountMain_error_le_log_of_hsw
    (hc : ∀ t : ℝ, 3000000000000 ≤ t →
      |(Ncount 0 t : ℝ) - t / (2 * Real.pi) * Real.log (t / (2 * Real.pi * Real.exp 1))| ≤
        0.1038 * Real.log t + 0.2573 * Real.log (Real.log t) + 9.3675)
    (t : ℝ) (ht : 3000000000000 ≤ t) :
    |(Ncount 0 t : ℝ) - tailCountMain t| ≤ Real.log t := by
  have ht0 : 0 < t := by linarith
  have ha : 0 < 2 * Real.pi := by positivity
  have hl := Real.log_le_log (by norm_num : 0 < (2 : ℝ) ^ 40)
    ((by norm_num : (2 : ℝ) ^ 40 ≤ 3000000000000).trans ht)
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hlt : 20 ≤ Real.log t := by linarith [Real.log_two_gt_d9]
  have hlog : Real.log (Real.log t) ≤ Real.log t - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  have h := hc t ht
  rw [← div_div t (2 * Real.pi) (Real.exp 1),
    Real.log_div (div_pos ht0 ha).ne' (Real.exp_pos 1).ne', Real.log_exp] at h
  exact h.trans (by linarith)

end RiemannResearch.Analysis.ActualZeroOrdinate
