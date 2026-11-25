/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.MontgomeryPrimeDiagonalAsymptotic
import RiemannResearch.Analysis.MontgomeryPrimeDiagonalTransition
import RiemannResearch.Analysis.MontgomeryPrimeDiagonalAbel
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # The unconditional prime-signal mean square

A frequency integral of the upper-cutoff branch bounds the weighted square
sum in the Montgomery–Vaughan mean-value inequality. The existing asymptotic
for the ordinary prime diagonal supplies the entire arithmetic input.
The frequency-slice proof is also recorded in
`RiemannResearch/RH/MontgomerySecondOrderTransition20261119.md`, in its
discussion of the weighted Hilbert inequality. The target is the prime-signal component in BGSTB §3, equation (3.5),
https://arxiv.org/html/2501.14545v3#S3.E4.
-/

noncomputable section
open Filter Set MeasureTheory
open scoped Topology BigOperators ArithmeticFunction
namespace RiemannResearch.Analysis.MontgomeryHorizontalBessel
open MontgomeryPrimeCrossIntegral MontgomeryHorizontalTransfer

private def frequencySlice (x : ℝ) (n : ℕ) : ℝ → ℝ :=
  (Ioi (max x (n : ℝ))).indicator (fun y : ℝ => (Λ n)^2 * (n : ℝ) / y^4)

private theorem frequencySlice_integrable {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Integrable (frequencySlice x n) := by
  apply (integrable_indicator_iff measurableSet_Ioi).2
  have h := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-4 : ℝ) < -1)
    (hx.trans_le (le_max_left x (n : ℝ)))).const_mul ((Λ n)^2 * (n : ℝ))
  simpa [IntegrableOn, div_eq_mul_inv] using h

private theorem integral_frequencySlice {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (∫ y, frequencySlice x n y) = (Λ n)^2 * (n : ℝ) / (3 * (max x (n : ℝ))^3) := by
  have hp := hx.trans_le (le_max_left x (n : ℝ))
  rw [frequencySlice, integral_indicator measurableSet_Ioi]
  have he := integral_Ioi_rpow_of_lt (by norm_num : (-4 : ℝ) < -1) hp
  rw [show (-4 : ℝ) + 1 = -3 by norm_num] at he
  have h4 (t : ℝ) : t ^ (-4 : ℝ) = (t ^ 4)⁻¹ := by simp
  have h3 (t : ℝ) : t ^ (-3 : ℝ) = (t ^ 3)⁻¹ := by simp
  simp only [h4, h3] at he
  simp only [div_eq_mul_inv, integral_const_mul]
  rw [he]
  ring

/-- For n above x the frequency integral gives the entire weighted coefficient
exactly. For n at or below x it contributes the surplus (x-n) w_x(n)^2. -/
theorem weighted_primeWeight_sq_add_surplus {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (n : ℝ) * (primeWeight x n)^2 + max (x - n) 0 * (primeWeight x n)^2 =
      3 * x^2 * ((Λ n)^2 * (n : ℝ) / (3 * (max x (n : ℝ))^3)) := by
  rw [primeWeight_sq_edge_kernel hx]
  by_cases hn : (n : ℝ) ≤ x
  · rw [if_pos hn, max_eq_left (sub_nonneg.mpr hn), max_eq_left hn]
    field_simp [hx.ne'] <;> ring
  · have hnx := lt_of_not_ge hn
    rw [if_neg hn, max_eq_right (sub_nonpos.mpr hnx.le), max_eq_right hnx.le]
    field_simp [(hx.trans hnx).ne'] <;> ring

private theorem integral_log_envelope {x J : ℝ} (hx : 2 ≤ x) (hJ : 0 ≤ J) :
    IntegrableOn (fun y : ℝ => (Real.log y + J) / y^2) (Ioi x) ∧
      (∫ y in Ioi x, (Real.log y + J) / y^2) = (Real.log x + J + 1) / x := by
  let F (y : ℝ) := -((Real.log y + J + 1) / y)
  have hd (y : ℝ) (hy : y ∈ Ici x) : HasDerivAt F ((Real.log y + J) / y^2) y := by
    have hp : 0 < y := lt_of_lt_of_le (by linarith : 0 < x) hy
    have h := (((((Real.hasDerivAt_log hp.ne').add_const J).add_const 1).div
      (hasDerivAt_id y) hp.ne')).neg
    apply h.congr_deriv
    dsimp
    field_simp [hp.ne'] <;> ring
  have hn (y : ℝ) (hy : y ∈ Ioi x) : 0 ≤ (Real.log y + J) / y^2 :=
    div_nonneg (add_nonneg (Real.log_nonneg ((by linarith : 1 ≤ x).trans hy.le)) hJ)
      (sq_nonneg _)
  have hl := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hi : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hF : Tendsto F atTop (𝓝 0) := by
    have hlim := ((hl.add (hi.const_mul J)).add (hi.const_mul 1)).neg
    simp only [mul_zero, add_zero, neg_zero] at hlim
    apply hlim.congr' (Eventually.of_forall fun y => ?_)
    dsimp [F]
    ring
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hd hn hF, ?_⟩
  simpa [F] using integral_Ioi_of_hasDerivAt_of_nonneg' hd hn hF

/-- A uniform upper bound on the ordinary prime diagonal gives an O(x log x)
bound for its weighted square sum. The bound is valid at each real cutoff. -/
theorem weighted_primeWeight_sum_le_of_diagonal {J x : ℝ} (hJ : 0 ≤ J)
    (hd : ∀ y : ℝ, 2 ≤ y → primeDiagonal y - Real.log y ≤ J) (hx : 2 ≤ x) :
    (∑' n : ℕ, (n : ℝ) * (primeWeight x n)^2) ≤ 3 * x * (Real.log x + J + 1) := by
  have hp : 0 < x := by linarith
  have henv := integral_log_envelope hx hJ
  apply le_of_tendsto' (summable_weighted_primeWeight_sq hp).hasSum.tendsto_sum_nat
  intro N
  let s := Finset.range N
  have hpoint (y : ℝ) : (∑ n ∈ s, frequencySlice x n y) ≤
      (Ioi x).indicator (fun t : ℝ => (Real.log t + J) / t^2) y := by
    by_cases hy : x < y
    · rw [Set.indicator_of_mem (show y ∈ Ioi x from hy)]
      have hyp := hp.trans hy
      have hsum : Summable (fun n : ℕ => (primeWeight y n)^2) := by
        apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _
          (summable_weighted_primeWeight_sq hyp)
        intro n
        rcases eq_or_ne n 0 with rfl | hn
        · simp [primeWeight]
        · exact le_mul_of_one_le_left (sq_nonneg _) (by exact_mod_cast Nat.pos_of_ne_zero hn)
      calc
        _ ≤ ∑ n ∈ s, (primeWeight y n)^2 / y^2 := Finset.sum_le_sum fun n _ => by
          by_cases hn : max x (n : ℝ) < y
          · rw [frequencySlice, Set.indicator_of_mem (show y ∈ Ioi _ from hn),
              primeWeight_sq_edge_kernel hyp, if_pos ((le_max_right _ _).trans hn.le)]
            field_simp [hyp.ne']
            ring_nf
            exact le_rfl
          · rw [frequencySlice, Set.indicator_of_notMem (show y ∉ Ioi _ from hn)]
            positivity
        _ ≤ primeDiagonal y / y^2 := by
          rw [← Finset.sum_div]
          exact div_le_div_of_nonneg_right (hsum.sum_le_tsum _ fun _ _ => sq_nonneg _) (sq_nonneg _)
        _ ≤ _ := div_le_div_of_nonneg_right (by linarith only [hd y (hx.trans hy.le)]) (sq_nonneg _)
    · rw [Set.indicator_of_notMem (show y ∉ Ioi x from hy)]
      apply le_of_eq
      exact Finset.sum_eq_zero fun n _ => Set.indicator_of_notMem
        (show y ∉ Ioi (max x (n : ℝ)) from fun hn => hy ((le_max_left _ _).trans_lt hn)) _
  have hs := integral_mono (integrable_finsetSum s (fun n _ => frequencySlice_integrable hp n))
    ((integrable_indicator_iff measurableSet_Ioi).2 henv.1) hpoint
  rw [integral_finsetSum _ (fun n _ => frequencySlice_integrable hp n),
    integral_indicator measurableSet_Ioi, henv.2] at hs
  calc
    (∑ n ∈ s, (n : ℝ) * (primeWeight x n)^2) ≤ ∑ n ∈ s, 3 * x^2 * (∫ y, frequencySlice x n y) :=
      Finset.sum_le_sum fun n _ => by
        rw [integral_frequencySlice hp, ← weighted_primeWeight_sq_add_surplus hp]
        exact le_add_of_nonneg_right (mul_nonneg (le_max_right _ _) (sq_nonneg _))
    _ = 3 * x^2 * (∑ n ∈ s, ∫ y, frequencySlice x n y) := (Finset.mul_sum ..).symm
    _ ≤ _ := (mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 3 * x^2)).trans_eq
      (by field_simp [hp.ne'])

/-- The actual infinite prime signal satisfies the BGSTB arithmetic mean-square
component at every positive height and every cutoff x≥2. -/
theorem primeMeanSquare_error_le_linear_log :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T x : ℝ, 0 ≤ T → 2 ≤ x →
      |primeSignalEnergy T x - T * primeDiagonal x| ≤ C * x * Real.log (2*x) := by
  obtain ⟨J, hJ, hd⟩ := primeDiagonalBound_unconditional
  have h2 := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
  let D := 1 + (J + 1) / Real.log 2
  refine ⟨117 * D, by dsimp [D]; positivity, ?_⟩
  intro T x hT hx
  have hp : 0 < x := by linarith
  have hw := weighted_primeWeight_sum_le_of_diagonal hJ
    (fun y hy => (abs_le.mp (hd y hy)).2) hx
  have hlog : Real.log x + J + 1 ≤ D * Real.log (2*x) := by
    have h₁ := Real.log_le_log hp (show x ≤ 2*x by linarith)
    have h₂ := mul_le_mul_of_nonneg_left (Real.log_le_log (by norm_num : (0:ℝ)<2)
      (show 2 ≤ 2*x by linarith)) (div_nonneg (by linarith : 0 ≤ J + 1) h2.le)
    rw [div_mul_cancel₀ _ h2.ne'] at h₂
    dsimp [D]
    linarith only [h₁, h₂]
  calc
    _ ≤ 39 * _ := primeMeanSquare_error_le_weighted_sum hp hT
    _ ≤ 39 * (3*x*(Real.log x + J + 1)) := mul_le_mul_of_nonneg_left hw (by norm_num)
    _ ≤ 39 * (3*x*(D*Real.log (2*x))) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hlog (by positivity)) (by norm_num)
    _ = _ := by ring

/-- The prime arithmetic premise of the corrected positive-cutoff transition. -/
theorem primeSignalMeanSquareSource_unconditional : PrimeSignalMeanSquareSource := by
  obtain ⟨C, hC, hM⟩ := primeMeanSquare_error_le_linear_log
  obtain ⟨J, hJ, hd⟩ := primeDiagonalBound_unconditional
  refine ⟨max C J, hC.trans (le_max_left _ _), ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  intro x hx
  have hp : 0 ≤ x := by linarith [hx.1]
  have hlog : 0 ≤ Real.log (2*x) := Real.log_nonneg (by linarith [hx.1])
  have he : |T * primeDiagonal x - T * Real.log x| ≤ T * J := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hT]
    exact mul_le_mul_of_nonneg_left (hd x hx.1) hT
  calc
    _ ≤ |primeSignalEnergy T x - T * primeDiagonal x| +
        |T * primeDiagonal x - T * Real.log x| := abs_sub_le _ _ _
    _ ≤ C*x*Real.log (2*x) + T*J := add_le_add (hM T x hT hx.1) he
    _ ≤ _ := by
      rw [mul_add]
      linarith only [mul_le_mul_of_nonneg_right (le_max_left C J) (mul_nonneg hp hlog),
        mul_le_mul_of_nonneg_right (le_max_right C J) hT]

/-- At any moving sublinear cutoff the normalized arithmetic signal follows
its normalized logarithmic frequency. This includes frequencies tending to
one from below. -/
theorem primeSignalEnergy_tendsto_of_sublinear_cutoff (x : ℝ → ℝ) {α : ℝ}
    (hx : ∀ᶠ T : ℝ in atTop, 2 ≤ x T)
    (hr : Tendsto (fun T : ℝ => x T / T) atTop (𝓝 0))
    (ha : Tendsto (fun T : ℝ => Real.log (x T) / Real.log T) atTop (𝓝 α)) :
    Tendsto (fun T : ℝ => primeSignalEnergy T (x T) / (T * Real.log T)) atTop (𝓝 α) := by
  obtain ⟨J, _, hj⟩ := primeSignalMeanSquareSource_unconditional
  have hi : Tendsto (fun T : ℝ => (Real.log T)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hcost : Tendsto (fun T : ℝ => J * ((Real.log T)⁻¹ + (x T / T) *
      (Real.log 2 * (Real.log T)⁻¹ + Real.log (x T) / Real.log T))) atTop (𝓝 0) := by
    simpa using (hi.add (hr.mul ((hi.const_mul (Real.log 2)).add ha))).const_mul J
  have hdiff : Tendsto (fun T : ℝ => primeSignalEnergy T (x T)/(T*Real.log T) -
      Real.log (x T)/Real.log T) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hcost
    filter_upwards [hj, eventually_gt_atTop (1 : ℝ), hx,
      hr.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with T hT hT₁ hx₂ hrT
    have hTp := zero_lt_one.trans hT₁
    have hL := Real.log_pos hT₁
    have hxp : 0 < x T := by linarith only [hx₂]
    have hxT : x T ≤ T := by simpa only [one_mul] using ((div_lt_iff₀ hTp).mp hrT).le
    have he := hT (x T) ⟨hx₂,hxT⟩
    have hid : primeSignalEnergy T (x T)/(T*Real.log T) - Real.log (x T)/Real.log T =
        (primeSignalEnergy T (x T)-T*Real.log (x T))/(T*Real.log T) := by
      field_simp [hTp.ne', hL.ne']
    rw [Real.norm_eq_abs, hid, abs_div, abs_of_pos (mul_pos hTp hL)]
    calc
      _ ≤ J*(T+x T*Real.log (2*x T))/(T*Real.log T) :=
        div_le_div_of_nonneg_right he (mul_pos hTp hL).le
      _ = _ := by
        rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hxp.ne']
        field_simp [hTp.ne', hL.ne']
  simpa using hdiff.add ha

/-- The arithmetic signal has the predicted slope at each fixed interior frequency. -/
theorem primeSignalEnergy_tendsto_subunit {α : ℝ} (hα : 0 < α) (h₁ : α < 1) :
    Tendsto (fun T : ℝ => primeSignalEnergy T (T^α) / (T * Real.log T)) atTop (𝓝 α) := by
  apply primeSignalEnergy_tendsto_of_sublinear_cutoff (fun T => T^α)
    ((tendsto_rpow_atTop hα).eventually_ge_atTop 2)
  · have hpow : Tendsto (fun T : ℝ => T^(α-1)) atTop (𝓝 0) := by
      simpa only [neg_sub] using tendsto_rpow_neg_atTop (sub_pos.mpr h₁)
    apply hpow.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T ht
    rw [Real.rpow_sub ht, Real.rpow_one]
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T ht
    rw [Real.log_rpow (zero_lt_one.trans ht), mul_div_cancel_right₀ _ (Real.log_pos ht).ne']

/--
info: 'RiemannResearch.Analysis.MontgomeryHorizontalBessel.primeSignalMeanSquareSource_unconditional'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms primeSignalMeanSquareSource_unconditional

/--
info: 'RiemannResearch.Analysis.MontgomeryHorizontalBessel.primeSignalEnergy_tendsto_subunit'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms primeSignalEnergy_tendsto_subunit

end RiemannResearch.Analysis.MontgomeryHorizontalBessel
