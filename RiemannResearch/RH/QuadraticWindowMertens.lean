import RiemannResearch.RH.CanonicalMobiusStretchedEnergy
import RiemannResearch.RH.MertensLeeLeongCriterion
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Ordinary and reciprocal Möbius bounds for the quadratic-window test

Lee and Leong, arXiv:2208.06141v5, Theorem 1.1, equation (12) in the HTML,
provide the arithmetic estimate represented by the explicit input below.
Its logarithmic exponent absorbs any fixed multiple of the square root of
the logarithm. The project reciprocal-cutoff estimate then bounds both
Möbius sums required by the Pareto window.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto
open RiemannResearch.NumberTheory.PrimeNumberTheorem RiemannResearch.Analysis
open RiemannResearch.RH.QMertensFirstMoment

private theorem sqrt_log_le_mul_vk {D a : ℝ} (hD : 0 < D) (ha : 0 < a) :
    ∀ᶠ x : ℝ in atTop, D * Real.sqrt (Real.log x) ≤ a * vkProfile x := by
  have hr : Tendsto (fun t : ℝ => Real.log t / t ^ (1/2 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/2)).tendsto_div_nhds_zero
  have hrat : 0 < a/D := div_pos ha hD
  filter_upwards [Real.tendsto_log_atTop.eventually
    ((tendsto_order.1 hr).2 ((a/D)^5) (pow_pos hrat 5)),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop 1)] with x h hx
  let t := Real.log x
  have ht : 0 < t := zero_lt_one.trans hx
  have hl : 0 < Real.log t := Real.log_pos hx
  have hlog : Real.log t ≤ t^(1/2 : ℝ) * (a/D)^5 :=
    (div_lt_iff₀ (Real.rpow_pos_of_pos ht _)).mp h |>.le.trans_eq (mul_comm _ _)
  have hpow := Real.rpow_le_rpow hl.le hlog (by norm_num : (0:ℝ) ≤ 1/5)
  have hid : ((a/D)^5)^(1/5:ℝ) = a/D := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hrat.le]
    norm_num
  rw [Real.mul_rpow (Real.rpow_nonneg ht.le _) (pow_nonneg hrat.le _),
    ← Real.rpow_mul ht.le, hid] at hpow
  have hprod : t^(1/2:ℝ) * t^((1/2:ℝ)*(1/5:ℝ)) = t^(3/5:ℝ) := by
    rw [← Real.rpow_add ht]
    norm_num
  change D * Real.sqrt t ≤ a * (t^(3/5:ℝ) / (Real.log t)^(1/5:ℝ))
  rw [Real.sqrt_eq_rpow, ← mul_div_assoc, le_div_iff₀ (Real.rpow_pos_of_pos hl _)]
  calc
    _ ≤ (D*t^(1/2:ℝ)) * (t^((1/2:ℝ)*(1/5:ℝ)) * (a/D)) :=
      mul_le_mul_of_nonneg_left hpow (mul_nonneg hD.le (Real.rpow_nonneg ht.le _))
    _ = a * (t^(1/2:ℝ) * t^((1/2:ℝ)*(1/5:ℝ))) := by field_simp <;> ring
    _ = _ := by rw [hprod]

/-- At every fixed square-root-log coefficient, the published Mertens estimate
bounds the entire ordinary tail and the reciprocal partial sum together. -/
theorem mobius_quadratic_window_rates_of_leeLeong (hLL : LeeLeongMertensEstimate)
    (D : ℝ) (hD : 0 < D) :
    ∀ᶠ N : ℕ in atTop,
      let ε := 5 * Real.exp (-D * Real.sqrt (Real.log (N : ℝ)))
      (∀ t : ℕ, N ≤ t →
        |∑ d ∈ Finset.Icc 1 t, (ArithmeticFunction.moebius d : ℝ)| ≤ ε * (t : ℝ)) ∧
      |mobiusReciprocalSum N| ≤ ε := by
  let g := fun N : ℕ => Real.exp (-D * Real.sqrt (Real.log (N : ℝ)))
  have ha : 0 < leeLeongRate := Real.rpow_pos_of_pos (by norm_num) _
  have hraw : ∀ᶠ y : ℝ in atTop, |M y| ≤ Real.exp (-(2*D)*Real.sqrt (Real.log y)) * y := by
    filter_upwards [mertens_vk_of_leeLeong hLL,
      sqrt_log_le_mul_vk (D := 2*D) (by positivity) ha, eventually_ge_atTop (1:ℝ)] with y h hrate hy
    have hex := Real.exp_le_exp.mpr (neg_le_neg hrate)
    simp only [neg_mul] at *
    simp only [one_mul] at h
    exact h.trans (mul_le_mul_of_nonneg_right hex (zero_le_one.trans hy))
  obtain ⟨b, hb⟩ := eventually_atTop.1 hraw
  have hlim : Tendsto g atTop (𝓝 0) := by
    apply Real.tendsto_exp_comp_nhds_zero.mpr
    exact (Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop)).const_mul_atTop_of_neg (neg_lt_zero.mpr hD)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop b),
    hlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)), eventually_ge_atTop (1:ℕ)]
    with N hNb hsmall hN
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hg : 0 < g N := Real.exp_pos _
  have hsq : g N ^ 2 = Real.exp (-(2*D) * Real.sqrt (Real.log (N : ℝ))) := by
    dsimp only [g]; rw [sq, ← Real.exp_add]; congr 1; ring
  have htail (y : ℝ) (hy : (N:ℝ) ≤ y) : |M y| ≤ g N ^ 2 * y := by
    rw [hsq]
    apply (hb y (hNb.trans hy)).trans
    apply mul_le_mul_of_nonneg_right _ (hNR.le.trans hy)
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left (Real.sqrt_le_sqrt (Real.log_le_log hNR hy)) (by linarith)
  change (∀ t : ℕ, N ≤ t → _ ≤ 5 * g N * (t:ℝ)) ∧ _ ≤ 5 * g N
  refine ⟨?_, (canonicalMobius_energy_of_uniform_mertens_square N hN (g N) hg hsmall.le htail).1⟩
  intro t hNt
  have hi := M_nat_difference 0 t (Nat.zero_le t)
  have hset : Finset.Ioc 0 t = Finset.Icc 1 t := by
    ext k; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  have hz : M (0:ℝ) = 0 := by
    have hI : Finset.Iic (0:ℕ) = {0} := by ext k; simp
    simp [M, hI]
  rw [hset, Nat.cast_zero, hz, sub_zero] at hi
  rw [← hi]
  exact (htail t (by exact_mod_cast hNt)).trans (mul_le_mul_of_nonneg_right
    (by nlinarith [mul_nonneg hg.le (sub_nonneg.mpr hsmall.le)] : g N ^ 2 ≤ 5*g N)
    (Nat.cast_nonneg _))

end RiemannResearch.RH.Pareto
